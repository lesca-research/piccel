import pandas as pd
import logging

logger = logging.getLogger('Piccel')

class InconsistentIndex(Exception): pass

def conditional_set(df, column, value, other_df, other_col, other_values,
                    indexes):
    # TODO: add a lot of error catching and clear feedback
    if df.index.name != other_df.index.name:
        raise InconsistentIndex('Index of df (%s) is not the same as '\
                                'other_df (%s)' % (df.index.name,
                                                   other_df.index.name))

    other_mask = other_df[other_col].isin(other_values)
    other_selection = other_df[other_mask]
    extra = other_selection.index.difference(df.index)
    if len(extra) > 0:
        logger.warning('Index values in other but not in df: %s',
                       ', '.join(['%s' % e for e in extra]))
    # TODO: check that all index values in other mask are in df.index
    if indexes is not None:
        index_to_set = other_selection.index.intersection(indexes)
    else:
        index_to_set = other_selection.index
    df.loc[index_to_set, column] = value
