use std::collections::BTreeMap;

use indexmap::IndexMap;
use open_dds::data_connector::DataConnectorColumnName;
use open_dds::types::DataConnectorArgumentName;

use crate::error::{FieldError, FieldInternalError};
use plan_types::{
    AggregateFieldSelection, AggregateSelectionSet, Argument, Field, MutationArgument,
    MutationExecutionPlan, NestedArray, NestedField, NestedObject, OrderByDirection,
    OrderByElement, OrderByTarget, QueryExecutionPlan, QueryNode, Relationship,
    RelationshipArgument, ResolvedFilterExpression, VariableName,
};

#[derive(Debug, thiserror::Error)]
#[allow(clippy::enum_variant_names)]
pub enum NdcV01CompatibilityError {
    #[error("Nested relationships in expressions are not supported in NDC v0.1.x")]
    NestedRelationshipsInExpressionsNotSupported,

    #[error("Nested relationships in order by targets are not supported in NDC v0.1.x")]
    NestedRelationshipsInOrderByTargetsNotSupported,

    #[error("Comparisons against elements in scalar arrays are not supported in NDC v0.1.x")]
    NestedScalarArrayComparisonsNotSupported,

    #[error("Groupings are not supported in NDC v0.1.x")]
    GroupByNotSupported,
}

pub fn make_query_request(
    query_execution_plan: QueryExecutionPlan,
) -> Result<ndc_models_v01::QueryRequest, FieldError> {
    let query_request = ndc_models_v01::QueryRequest {
        collection: ndc_models_v01::CollectionName::from(query_execution_plan.collection.as_str()),
        query: make_query(query_execution_plan.query_node)?,
        arguments: make_arguments(query_execution_plan.arguments)?,
        collection_relationships: make_collection_relationships(
            query_execution_plan.collection_relationships,
        ),
        variables: make_variables(query_execution_plan.variables),
    };
    Ok(query_request)
}

pub fn make_mutation_request(
    mutation_execution_plan: MutationExecutionPlan,
) -> Result<ndc_models_v01::MutationRequest, FieldError> {
    let mutation_operation = ndc_models_v01::MutationOperation::Procedure {
        name: ndc_models_v01::ProcedureName::new(
            mutation_execution_plan.procedure_name.into_inner(),
        ),
        arguments: make_mutation_arguments(mutation_execution_plan.procedure_arguments)?,
        fields: mutation_execution_plan
            .procedure_fields
            .map(make_nested_field)
            .transpose()?,
    };

    let mutation_request = ndc_models_v01::MutationRequest {
        operations: vec![mutation_operation],
        collection_relationships: make_collection_relationships(
            mutation_execution_plan.collection_relationships,
        ),
    };

    Ok(mutation_request)
}
fn make_variables(
    variables: Option<Vec<BTreeMap<VariableName, serde_json::Value>>>,
) -> Option<Vec<BTreeMap<ndc_models_v01::VariableName, serde_json::Value>>> {
    variables.map(|variables| {
        variables
            .into_iter()
            .map(|variables_map| {
                variables_map
                    .into_iter()
                    .map(|(name, value)| {
                        (ndc_models_v01::VariableName::from(name.0.as_str()), value)
                    })
                    .collect()
            })
            .collect()
    })
}

fn make_query(query_node: QueryNode) -> Result<ndc_models_v01::Query, FieldError> {
    // Group by is not supported in 0.1.x
    if query_node.group_by.is_some() {
        return Err(FieldError::InternalError(
            FieldInternalError::NdcV01CompatibilityError(
                NdcV01CompatibilityError::GroupByNotSupported,
            ),
        ));
    }

    let ndc_predicate = query_node.predicate.map(make_expression).transpose()?;

    let ndc_fields = query_node
        .fields
        .map(|fields| {
            fields
                .fields
                .into_iter()
                .map(|(name, field)| {
                    Ok((
                        ndc_models_v01::FieldName::from(name.as_str()),
                        make_field(field)?,
                    ))
                })
                .collect::<Result<IndexMap<_, _>, FieldError>>()
        })
        .transpose()?;

    Ok(ndc_models_v01::Query {
        limit: query_node.limit,
        offset: query_node.offset,
        order_by: query_node.order_by.map(make_order_by).transpose()?,
        predicate: ndc_predicate,
        aggregates: query_node.aggregates.map(make_aggregates),
        fields: ndc_fields,
    })
}

fn make_arguments(
    arguments: BTreeMap<DataConnectorArgumentName, Argument>,
) -> Result<BTreeMap<ndc_models_v01::ArgumentName, ndc_models_v01::Argument>, FieldError> {
    arguments
        .into_iter()
        .map(|(name, argument)| {
            Ok((
                ndc_models_v01::ArgumentName::new(name.into_inner()),
                make_argument(argument)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()
}

fn make_argument(argument: Argument) -> Result<ndc_models_v01::Argument, FieldError> {
    match argument {
        Argument::Literal { value } => Ok(ndc_models_v01::Argument::Literal { value }),
        Argument::Variable { name } => Ok(ndc_models_v01::Argument::Variable {
            name: ndc_models_v01::VariableName::from(name.0.as_str()),
        }),
        Argument::BooleanExpression { predicate } => {
            let ndc_expression = make_expression(predicate)?;
            Ok(ndc_models_v01::Argument::Literal {
                value: serde_json::to_value(ndc_expression).map_err(|e| {
                    FieldError::InternalError(FieldInternalError::ExpressionSerializationError(e))
                })?,
            })
        }
    }
}

fn make_relationship_arguments_from_arguments(
    arguments: BTreeMap<DataConnectorArgumentName, Argument>,
) -> Result<BTreeMap<ndc_models_v01::ArgumentName, ndc_models_v01::RelationshipArgument>, FieldError>
{
    arguments
        .into_iter()
        .map(|(name, argument)| {
            Ok((
                ndc_models_v01::ArgumentName::new(name.into_inner()),
                make_relationship_argument_from_argument(argument)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()
}

fn make_relationship_argument_from_argument(
    argument: Argument,
) -> Result<ndc_models_v01::RelationshipArgument, FieldError> {
    match argument {
        Argument::Literal { value } => Ok(ndc_models_v01::RelationshipArgument::Literal { value }),
        Argument::Variable { name } => Ok(ndc_models_v01::RelationshipArgument::Variable {
            name: ndc_models_v01::VariableName::from(name.0.as_str()),
        }),
        Argument::BooleanExpression { predicate } => {
            let ndc_expression = make_expression(predicate)?;
            Ok(ndc_models_v01::RelationshipArgument::Literal {
                value: serde_json::to_value(ndc_expression).map_err(|e| {
                    FieldError::InternalError(FieldInternalError::ExpressionSerializationError(e))
                })?,
            })
        }
    }
}

fn make_relationship_arguments(
    arguments: BTreeMap<DataConnectorArgumentName, RelationshipArgument>,
) -> BTreeMap<ndc_models_v01::ArgumentName, ndc_models_v01::RelationshipArgument> {
    arguments
        .into_iter()
        .map(|(name, argument)| {
            (
                ndc_models_v01::ArgumentName::new(name.into_inner()),
                make_relationship_argument(argument),
            )
        })
        .collect::<BTreeMap<_, _>>()
}

fn make_relationship_argument(
    argument: RelationshipArgument,
) -> ndc_models_v01::RelationshipArgument {
    match argument {
        RelationshipArgument::Column { name } => ndc_models_v01::RelationshipArgument::Column {
            name: ndc_models_v01::FieldName::new(name.into_inner()),
        },
    }
}

fn make_expression(
    predicate: ResolvedFilterExpression,
) -> Result<ndc_models_v01::Expression, FieldError> {
    match predicate {
        ResolvedFilterExpression::And { expressions } => {
            let mut ndc_expressions = Vec::new();
            for expression in expressions {
                let ndc_expression = make_expression(expression)?;
                ndc_expressions.push(ndc_expression);
            }
            Ok(ndc_models_v01::Expression::And {
                expressions: ndc_expressions,
            })
        }
        ResolvedFilterExpression::Or { expressions } => {
            let mut ndc_expressions = Vec::new();
            for expression in expressions {
                let ndc_expression = make_expression(expression)?;
                ndc_expressions.push(ndc_expression);
            }
            Ok(ndc_models_v01::Expression::Or {
                expressions: ndc_expressions,
            })
        }
        ResolvedFilterExpression::Not { expression } => {
            let ndc_expression = make_expression(*expression)?;
            Ok(ndc_models_v01::Expression::Not {
                expression: Box::new(ndc_expression),
            })
        }
        ResolvedFilterExpression::LocalFieldComparison(
            plan_types::LocalFieldComparison::BinaryComparison {
                column,
                operator,
                value,
            },
        ) => Ok(ndc_models_v01::Expression::BinaryComparisonOperator {
            column: make_comparison_target(column),
            operator: ndc_models_v01::ComparisonOperatorName::new(operator.into_inner()),
            value: make_comparison_value(value),
        }),
        ResolvedFilterExpression::LocalNestedArray {
            column,
            field_path,
            predicate,
        } => {
            let ndc_expression = make_expression(*predicate)?;
            let field_name = ndc_models_v01::FieldName::new(column.into_inner());

            Ok(ndc_models_v01::Expression::Exists {
                in_collection: ndc_models_v01::ExistsInCollection::NestedCollection {
                    column_name: field_name,
                    field_path: field_path
                        .into_iter()
                        .map(|f| ndc_models_v01::FieldName::new(f.into_inner()))
                        .collect(),
                    arguments: BTreeMap::new(),
                },
                predicate: Some(Box::new(ndc_expression)),
            })
        }
        ResolvedFilterExpression::LocalNestedScalarArray { .. } => Err(FieldError::InternalError(
            FieldInternalError::NdcV01CompatibilityError(
                NdcV01CompatibilityError::NestedScalarArrayComparisonsNotSupported,
            ),
        )),
        ResolvedFilterExpression::LocalFieldComparison(
            plan_types::LocalFieldComparison::UnaryComparison { column, operator },
        ) => Ok(ndc_models_v01::Expression::UnaryComparisonOperator {
            column: make_comparison_target(column),
            operator: match operator {
                metadata_resolve::UnaryComparisonOperator::IsNull => {
                    ndc_models_v01::UnaryComparisonOperator::IsNull
                }
            },
        }),
        ResolvedFilterExpression::LocalRelationshipComparison {
            field_path,
            relationship,
            predicate,
        } => {
            if !field_path.is_empty() {
                return Err(FieldError::InternalError(
                    FieldInternalError::NdcV01CompatibilityError(
                        NdcV01CompatibilityError::NestedRelationshipsInExpressionsNotSupported,
                    ),
                ));
            }

            let ndc_expression = make_expression(*predicate)?;
            Ok(ndc_models_v01::Expression::Exists {
                in_collection: ndc_models_v01::ExistsInCollection::Related {
                    relationship: ndc_models_v01::RelationshipName::from(relationship.as_str()),
                    arguments: BTreeMap::new(),
                },
                predicate: Some(Box::new(ndc_expression)),
            })
        }
        // we are generating NDC request for one connector, we can ignore anything remote
        ResolvedFilterExpression::RemoteRelationshipComparison {
            remote_predicate_id: _,
        } => Ok(ndc_models_v01::Expression::And {
            expressions: vec![],
        }),
    }
}

fn make_comparison_target(
    comparison_target: plan_types::ComparisonTarget,
) -> ndc_models_v01::ComparisonTarget {
    match comparison_target {
        plan_types::ComparisonTarget::Column { name, field_path } => {
            ndc_models_v01::ComparisonTarget::Column {
                name: ndc_models_v01::FieldName::new(name.into_inner()),
                field_path: if field_path.is_empty() {
                    None
                } else {
                    Some(
                        field_path
                            .into_iter()
                            .map(|f| ndc_models_v01::FieldName::new(f.into_inner()))
                            .collect(),
                    )
                },
                path: vec![],
            }
        }
    }
}

fn make_comparison_value(
    comparison_value: plan_types::ComparisonValue,
) -> ndc_models_v01::ComparisonValue {
    match comparison_value {
        plan_types::ComparisonValue::Scalar { value } => {
            ndc_models_v01::ComparisonValue::Scalar { value }
        }
        plan_types::ComparisonValue::Variable { name } => {
            ndc_models_v01::ComparisonValue::Variable {
                name: ndc_models_v01::VariableName::from(name.0.as_str()),
            }
        }
    }
}

fn make_field(field: Field) -> Result<ndc_models_v01::Field, FieldError> {
    match field {
        Field::Column {
            column,
            fields,
            arguments,
        } => {
            let nested_fields = fields.map(make_nested_field).transpose()?;

            Ok(ndc_models_v01::Field::Column {
                column: ndc_models_v01::FieldName::new(column.into_inner()),
                fields: nested_fields,
                arguments: make_arguments(arguments)?,
            })
        }
        Field::Relationship {
            query_node,
            relationship,
            arguments,
        } => {
            let query = make_query(*query_node)?;
            Ok(ndc_models_v01::Field::Relationship {
                query: Box::new(query),
                relationship: ndc_models_v01::RelationshipName::from(relationship.as_str()),
                arguments: make_relationship_arguments_from_arguments(arguments)?,
            })
        }
    }
}

fn make_nested_field(nested_field: NestedField) -> Result<ndc_models_v01::NestedField, FieldError> {
    match nested_field {
        NestedField::Object(nested_object) => Ok(ndc_models_v01::NestedField::Object(
            make_nested_object(nested_object)?,
        )),
        NestedField::Array(nested_array) => Ok(ndc_models_v01::NestedField::Array(
            make_nested_array(nested_array)?,
        )),
    }
}

fn make_nested_object(
    nested_field: NestedObject,
) -> Result<ndc_models_v01::NestedObject, FieldError> {
    let fields = nested_field
        .fields
        .into_iter()
        .map(|(name, field)| {
            Ok((
                ndc_models_v01::FieldName::from(name.as_str()),
                make_field(field)?,
            ))
        })
        .collect::<Result<IndexMap<_, _>, FieldError>>()?;
    Ok(ndc_models_v01::NestedObject { fields })
}

fn make_nested_array(nested_field: NestedArray) -> Result<ndc_models_v01::NestedArray, FieldError> {
    let fields = make_nested_field(*nested_field.fields)?;
    Ok(ndc_models_v01::NestedArray {
        fields: Box::new(fields),
    })
}

fn make_collection_relationships(
    collection_relationships: BTreeMap<plan_types::NdcRelationshipName, Relationship>,
) -> BTreeMap<ndc_models_v01::RelationshipName, ndc_models_v01::Relationship> {
    collection_relationships
        .into_iter()
        .map(|(name, relationship)| {
            (
                ndc_models_v01::RelationshipName::from(name.as_str()),
                make_relationship(relationship),
            )
        })
        .collect::<BTreeMap<_, _>>()
}

fn make_relationship(relationship: Relationship) -> ndc_models_v01::Relationship {
    ndc_models_v01::Relationship {
        column_mapping: relationship
            .column_mapping
            .into_iter()
            .map(|(s, t)| {
                (
                    ndc_models_v01::FieldName::new(s.into_inner()),
                    ndc_models_v01::FieldName::new(t.into_inner()),
                )
            })
            .collect(),
        relationship_type: match relationship.relationship_type {
            open_dds::relationships::RelationshipType::Object => {
                ndc_models_v01::RelationshipType::Object
            }
            open_dds::relationships::RelationshipType::Array => {
                ndc_models_v01::RelationshipType::Array
            }
        },
        target_collection: ndc_models_v01::CollectionName::new(
            relationship.target_collection.into_inner(),
        ),
        arguments: make_relationship_arguments(relationship.arguments),
    }
}

fn make_order_by(
    order_by_elements: Vec<OrderByElement<ResolvedFilterExpression>>,
) -> Result<ndc_models_v01::OrderBy, FieldError> {
    Ok(ndc_models_v01::OrderBy {
        elements: order_by_elements
            .into_iter()
            .map(|element| {
                Ok(ndc_models_v01::OrderByElement {
                    order_direction: match element.order_direction {
                        OrderByDirection::Asc => ndc_models_v01::OrderDirection::Asc,
                        OrderByDirection::Desc => ndc_models_v01::OrderDirection::Desc,
                    },
                    target: make_order_by_target(element.target)?,
                })
            })
            .collect::<Result<Vec<_>, FieldError>>()?,
    })
}

fn make_order_by_target(
    target: OrderByTarget<ResolvedFilterExpression>,
) -> Result<ndc_models_v01::OrderByTarget, FieldError> {
    match target {
        OrderByTarget::Column {
            name,
            field_path,
            relationship_path,
        } => {
            let mut order_by_element_path = Vec::new();
            // When using a nested relationship column, you'll have to provide all the relationships(paths)
            // NDC has to traverse to access the column. The ordering of that paths is important.
            // The order decides how to access the column.
            //
            // For example, if you have a model called `User` with a relationship column called `Posts`
            // which has a relationship column called `Comments` which has a non-relationship column
            // called `text`, you'll have to provide the following paths to access the `text` column:
            // ["UserPosts", "PostsComments"]
            for path_element in relationship_path {
                if !path_element.field_path.is_empty() {
                    return Err(FieldError::InternalError(
                        FieldInternalError::NdcV01CompatibilityError(
                            NdcV01CompatibilityError::NestedRelationshipsInOrderByTargetsNotSupported,
                        ),
                    ));
                }

                order_by_element_path.push(ndc_models_v01::PathElement {
                    relationship: ndc_models_v01::RelationshipName::from(
                        path_element.relationship_name.as_str(),
                    ),
                    arguments: BTreeMap::new(),
                    predicate: match path_element.filter_predicate {
                        Some(predicate) => Some(Box::new(make_expression(predicate)?)),
                        // We convert all None predicates into an always true predicate to work
                        // around a bug in the postgres connector
                        None => Some(Box::new(ndc_models_v01::Expression::And {
                            expressions: vec![],
                        })),
                    },
                });
            }

            Ok(ndc_models_v01::OrderByTarget::Column {
                name: ndc_models_v01::FieldName::new(name.into_inner()),
                path: order_by_element_path,
                field_path: if field_path.is_empty() {
                    None
                } else {
                    Some(
                        field_path
                            .iter()
                            .map(|name| ndc_models_v01::FieldName::from(name.as_str()))
                            .collect(),
                    )
                },
            })
        }
    }
}

/// Translates the internal IR 'AggregateSelectionSet' into an NDC query aggregates selection
fn make_aggregates(
    aggregate_selection_set: AggregateSelectionSet,
) -> IndexMap<ndc_models_v01::FieldName, ndc_models_v01::Aggregate> {
    aggregate_selection_set
        .fields
        .into_iter()
        .map(|(field_name, aggregate_selection)| {
            let aggregate = match aggregate_selection {
                AggregateFieldSelection::Count { column_path, .. } => {
                    make_count_aggregate(column_path, false)
                }
                AggregateFieldSelection::CountDistinct { column_path, .. } => {
                    make_count_aggregate(column_path, true)
                }
                AggregateFieldSelection::AggregationFunction {
                    function_name,
                    column_path,
                } => {
                    let nonempty::NonEmpty {
                        head: column,
                        tail: field_path,
                    } = column_path;
                    let nested_field_path = field_path
                        .into_iter()
                        .map(|column_name| {
                            ndc_models_v01::FieldName::from(column_name.into_inner())
                        })
                        .collect::<Vec<_>>();
                    ndc_models_v01::Aggregate::SingleColumn {
                        column: ndc_models_v01::FieldName::from(column.into_inner()),
                        field_path: if nested_field_path.is_empty() {
                            None
                        } else {
                            Some(nested_field_path)
                        },
                        function: ndc_models_v01::AggregateFunctionName::from(
                            function_name.as_str(),
                        ),
                    }
                }
            };
            (
                ndc_models_v01::FieldName::from(field_name.as_str()),
                aggregate,
            )
        })
        .collect()
}

/// Creates the appropriate NDC count aggregation based on whether we're selecting
/// a column (nested or otherwise) or not
fn make_count_aggregate(
    column_path: Vec<DataConnectorColumnName>,
    distinct: bool,
) -> ndc_models_v01::Aggregate {
    let mut column_path_iter = column_path.into_iter();
    if let Some(first_path_element) = column_path_iter.next() {
        let remaining_path = column_path_iter
            .map(|column_name| ndc_models_v01::FieldName::from(column_name.into_inner()))
            .collect::<Vec<_>>();
        let nested_field_path = if remaining_path.is_empty() {
            None
        } else {
            Some(remaining_path)
        };
        ndc_models_v01::Aggregate::ColumnCount {
            column: ndc_models_v01::FieldName::from(first_path_element.into_inner()),
            field_path: nested_field_path,
            distinct,
        }
    } else {
        ndc_models_v01::Aggregate::StarCount {}
    }
}

fn make_mutation_arguments(
    arguments: BTreeMap<DataConnectorArgumentName, MutationArgument>,
) -> Result<BTreeMap<ndc_models_v01::ArgumentName, serde_json::Value>, FieldError> {
    arguments
        .into_iter()
        .map(|(name, argument)| {
            Ok((
                ndc_models_v01::ArgumentName::new(name.into_inner()),
                make_mutation_argument(argument)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()
}

fn make_mutation_argument(argument: MutationArgument) -> Result<serde_json::Value, FieldError> {
    match argument {
        MutationArgument::Literal { value } => Ok(value),
        MutationArgument::BooleanExpression { predicate } => {
            let ndc_expression = make_expression(predicate)?;
            Ok(serde_json::to_value(ndc_expression).map_err(|e| {
                FieldError::InternalError(FieldInternalError::ExpressionSerializationError(e))
            })?)
        }
    }
}
