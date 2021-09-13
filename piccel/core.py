import pandas as pd

class LazyFunc:
    def __init__(self, func, *args, **kwargs):
        self.func = func
        self.args = args
        self.kwargs = kwargs
    def __call__(self, **kwargs):
        return self.func(*self.args, **{**self.kwargs, **kwargs})

def df_index_from_value(df, value_dict):
    if len(value_dict) == 0:
        return []
    # iter_vd = iter(value_dict.items())
    # first_key, first_value = next(iter_vd)
    # m = df[first_key] == first_value
    # for key, value in iter_vd:
    #     m &= (df[key] == value)
    return df_filter_from_dict(df, value_dict).index.to_list()

def df_filter_from_dict(df, value_dict):
    return df.loc[(df[list(value_dict)] == pd.Series(value_dict)).all(axis=1)]
