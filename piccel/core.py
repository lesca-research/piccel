
class LazyFunc:
    def __init__(self, func, *args, **kwargs):
        self.func = func
        self.args = args
        self.kwargs = kwargs
    def __call__(self, **kwargs):
        return self.func(*self.args, **{**self.kwargs, **kwargs})
