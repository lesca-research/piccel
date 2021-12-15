import sys
import logging

logger = logging.getLogger('piccel')
console_handler = logging.StreamHandler(stream=sys.stdout)
fmt = '%(name)s | %(asctime)s %(levelname)-8s  %(message)s'
console_handler.setFormatter(logging.Formatter(fmt=fmt,
                                               datefmt='%Y-%m-%d %H:%M:%S'))
logger.addHandler(console_handler)

DEBUG_LEVEL2_NUM = 9
logging.addLevelName(DEBUG_LEVEL2_NUM, "DEBUG2")
def debug2(self, message, *args, **kws):
    if self.isEnabledFor(DEBUG_LEVEL2_NUM):
        # Yes, logger takes its '*args' as 'args'.
        self._log(DEBUG_LEVEL2_NUM, message, args, **kws)
logging.Logger.debug2 = debug2

DEBUG_LEVEL3_NUM = 8
logging.addLevelName(DEBUG_LEVEL3_NUM, "DEBUG3")
def debug3(self, message, *args, **kws):
    if self.isEnabledFor(DEBUG_LEVEL3_NUM):
        # Yes, logger takes its '*args' as 'args'.
        self._log(DEBUG_LEVEL3_NUM, message, args, **kws)
logging.Logger.debug3 = debug3
