
# encoding: utf-8

# *** GENERATED BY `setup.py antlr`, DO NOT EDIT BY HAND ***
#
# Generated from ../LaTeX.g4, derived from latex2sympy
#     latex2sympy is licensed under the MIT license
#     https://github.com/augustt198/latex2sympy/blob/master/LICENSE.txt
#
# Generated with antlr4
#    antlr4 is licensed under the BSD-3-Clause License
#    https://github.com/antlr/antlr4/blob/master/LICENSE.txt
from __future__ import print_function
from antlr4 import *
from io import StringIO
import sys



def serializedATN():
    with StringIO() as buf:
        buf.write(u"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2")
        buf.write(u"Y\u0384\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4")
        buf.write(u"\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\4\f\t\f\4\r")
        buf.write(u"\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22")
        buf.write(u"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4")
        buf.write(u"\30\t\30\4\31\t\31\4\32\t\32\4\33\t\33\4\34\t\34\4\35")
        buf.write(u"\t\35\4\36\t\36\4\37\t\37\4 \t \4!\t!\4\"\t\"\4#\t#\4")
        buf.write(u"$\t$\4%\t%\4&\t&\4\'\t\'\4(\t(\4)\t)\4*\t*\4+\t+\4,\t")
        buf.write(u",\4-\t-\4.\t.\4/\t/\4\60\t\60\4\61\t\61\4\62\t\62\4\63")
        buf.write(u"\t\63\4\64\t\64\4\65\t\65\4\66\t\66\4\67\t\67\48\t8\4")
        buf.write(u"9\t9\4:\t:\4;\t;\4<\t<\4=\t=\4>\t>\4?\t?\4@\t@\4A\tA")
        buf.write(u"\4B\tB\4C\tC\4D\tD\4E\tE\4F\tF\4G\tG\4H\tH\4I\tI\4J\t")
        buf.write(u"J\4K\tK\4L\tL\4M\tM\4N\tN\4O\tO\4P\tP\4Q\tQ\4R\tR\4S")
        buf.write(u"\tS\4T\tT\4U\tU\4V\tV\4W\tW\4X\tX\4Y\tY\4Z\tZ\3\2\3\2")
        buf.write(u"\3\3\6\3\u00b9\n\3\r\3\16\3\u00ba\3\3\3\3\3\4\3\4\3\4")
        buf.write(u"\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\5\4\u00cb\n\4\3")
        buf.write(u"\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\5\5")
        buf.write(u"\5\u00da\n\5\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6")
        buf.write(u"\3\6\3\6\3\6\3\6\3\6\5\6\u00eb\n\6\3\6\3\6\3\7\3\7\3")
        buf.write(u"\7\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3")
        buf.write(u"\b\3\b\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3\t\3")
        buf.write(u"\t\3\t\3\t\3\t\5\t\u010f\n\t\3\t\3\t\3\n\3\n\3\n\3\n")
        buf.write(u"\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\13\3\13")
        buf.write(u"\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3")
        buf.write(u"\13\3\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3")
        buf.write(u"\f\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\r\3\16\3\16\3\16")
        buf.write(u"\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3")
        buf.write(u"\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16")
        buf.write(u"\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3")
        buf.write(u"\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16\3\16")
        buf.write(u"\3\16\3\16\3\16\3\16\3\16\3\16\5\16\u0177\n\16\3\16\3")
        buf.write(u"\16\3\17\3\17\3\20\3\20\3\21\3\21\3\22\3\22\3\23\3\23")
        buf.write(u"\3\24\3\24\3\25\3\25\3\26\3\26\3\27\3\27\3\27\3\30\3")
        buf.write(u"\30\3\30\3\31\3\31\3\32\3\32\3\33\3\33\3\34\3\34\3\34")
        buf.write(u"\3\34\3\34\3\34\3\34\3\34\3\35\3\35\3\35\3\35\3\35\3")
        buf.write(u"\35\3\35\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\37")
        buf.write(u"\3\37\3\37\3\37\3\37\3\37\3\37\3\37\3 \3 \3 \3 \3 \3")
        buf.write(u"!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!")
        buf.write(u"\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3")
        buf.write(u"!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!\3!")
        buf.write(u"\3!\3!\5!\u01f2\n!\3\"\3\"\3\"\3\"\3\"\3#\3#\3#\3#\3")
        buf.write(u"#\3$\3$\3$\3$\3$\3$\3%\3%\3%\3%\3%\3&\3&\3&\3&\3&\3\'")
        buf.write(u"\3\'\3\'\3\'\3(\3(\3(\3(\3(\3)\3)\3)\3)\3)\3*\3*\3*\3")
        buf.write(u"*\3*\3+\3+\3+\3+\3+\3,\3,\3,\3,\3,\3-\3-\3-\3-\3-\3.")
        buf.write(u"\3.\3.\3.\3.\3.\3.\3.\3/\3/\3/\3/\3/\3/\3/\3/\3\60\3")
        buf.write(u"\60\3\60\3\60\3\60\3\60\3\60\3\60\3\61\3\61\3\61\3\61")
        buf.write(u"\3\61\3\61\3\61\3\61\3\62\3\62\3\62\3\62\3\62\3\62\3")
        buf.write(u"\62\3\62\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\63\3\64")
        buf.write(u"\3\64\3\64\3\64\3\64\3\64\3\65\3\65\3\65\3\65\3\65\3")
        buf.write(u"\65\3\66\3\66\3\66\3\66\3\66\3\66\3\67\3\67\3\67\3\67")
        buf.write(u"\3\67\3\67\3\67\3\67\38\38\38\38\38\38\38\38\39\39\3")
        buf.write(u"9\39\39\39\39\39\3:\3:\3:\3:\3:\3:\3:\3:\3;\3;\3;\3;")
        buf.write(u"\3;\3;\3;\3;\3<\3<\3<\3<\3<\3<\3<\3=\3=\3=\3=\3=\3=\3")
        buf.write(u"=\3>\3>\3>\3>\3>\3>\3?\3?\3?\3?\3?\3?\3?\3@\3@\3@\3@")
        buf.write(u"\3@\3@\3A\3A\3A\3A\3A\3B\3B\3B\3B\3B\3B\3C\3C\3C\3C\3")
        buf.write(u"C\3C\3C\3D\3D\3D\3D\3D\3D\3D\3D\3E\3E\3E\3E\3E\3E\3E")
        buf.write(u"\3E\3F\3F\3F\3F\3F\3F\3F\3F\3G\3G\3H\3H\3I\3I\3J\3J\3")
        buf.write(u"K\3K\7K\u02ef\nK\fK\16K\u02f2\13K\3K\3K\3K\6K\u02f7\n")
        buf.write(u"K\rK\16K\u02f8\5K\u02fb\nK\3L\3L\3M\3M\3N\6N\u0302\n")
        buf.write(u"N\rN\16N\u0303\3N\3N\3N\3N\3N\7N\u030b\nN\fN\16N\u030e")
        buf.write(u"\13N\3N\7N\u0311\nN\fN\16N\u0314\13N\3N\3N\3N\3N\3N\7")
        buf.write(u"N\u031b\nN\fN\16N\u031e\13N\3N\3N\6N\u0322\nN\rN\16N")
        buf.write(u"\u0323\5N\u0326\nN\3O\3O\7O\u032a\nO\fO\16O\u032d\13")
        buf.write(u"O\5O\u032f\nO\3O\3O\3O\7O\u0334\nO\fO\16O\u0337\13O\3")
        buf.write(u"O\5O\u033a\nO\5O\u033c\nO\3P\3P\3P\3P\3P\3Q\3Q\3R\3R")
        buf.write(u"\3R\3R\3R\3R\3R\3R\3R\5R\u034e\nR\3S\3S\3S\3S\3S\3S\3")
        buf.write(u"T\3T\3T\3T\3T\3T\3T\3T\3T\3T\3U\3U\3V\3V\3V\3V\3V\3V")
        buf.write(u"\3V\3V\3V\5V\u036b\nV\3W\3W\3W\3W\3W\3W\3X\3X\3X\3X\3")
        buf.write(u"X\3X\3X\3X\3X\3X\3Y\3Y\3Z\3Z\6Z\u0381\nZ\rZ\16Z\u0382")
        buf.write(u"\5\u02f0\u032b\u0335\2[\3\3\5\4\7\5\t\6\13\7\r\b\17\t")
        buf.write(u"\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22#\23")
        buf.write(u"%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36")
        buf.write(u";\37= ?!A\"C#E$G%I&K\'M(O)Q*S+U,W-Y.[/]\60_\61a\62c\63")
        buf.write(u"e\64g\65i\66k\67m8o9q:s;u<w=y>{?}@\177A\u0081B\u0083")
        buf.write(u"C\u0085D\u0087E\u0089F\u008bG\u008dH\u008fI\u0091J\u0093")
        buf.write(u"\2\u0095K\u0097L\u0099\2\u009bM\u009dN\u009fO\u00a1P")
        buf.write(u"\u00a3Q\u00a5R\u00a7S\u00a9T\u00abU\u00adV\u00afW\u00b1")
        buf.write(u"X\u00b3Y\3\2\5\5\2\13\f\17\17\"\"\4\2C\\c|\3\2\62;\2")
        buf.write(u"\u03ab\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2")
        buf.write(u"\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2")
        buf.write(u"\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2")
        buf.write(u"\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2")
        buf.write(u"#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2")
        buf.write(u"\2\2-\3\2\2\2\2/\3\2\2\2\2\61\3\2\2\2\2\63\3\2\2\2\2")
        buf.write(u"\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2\2\2\2=\3\2")
        buf.write(u"\2\2\2?\3\2\2\2\2A\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3")
        buf.write(u"\2\2\2\2I\3\2\2\2\2K\3\2\2\2\2M\3\2\2\2\2O\3\2\2\2\2")
        buf.write(u"Q\3\2\2\2\2S\3\2\2\2\2U\3\2\2\2\2W\3\2\2\2\2Y\3\2\2\2")
        buf.write(u"\2[\3\2\2\2\2]\3\2\2\2\2_\3\2\2\2\2a\3\2\2\2\2c\3\2\2")
        buf.write(u"\2\2e\3\2\2\2\2g\3\2\2\2\2i\3\2\2\2\2k\3\2\2\2\2m\3\2")
        buf.write(u"\2\2\2o\3\2\2\2\2q\3\2\2\2\2s\3\2\2\2\2u\3\2\2\2\2w\3")
        buf.write(u"\2\2\2\2y\3\2\2\2\2{\3\2\2\2\2}\3\2\2\2\2\177\3\2\2\2")
        buf.write(u"\2\u0081\3\2\2\2\2\u0083\3\2\2\2\2\u0085\3\2\2\2\2\u0087")
        buf.write(u"\3\2\2\2\2\u0089\3\2\2\2\2\u008b\3\2\2\2\2\u008d\3\2")
        buf.write(u"\2\2\2\u008f\3\2\2\2\2\u0091\3\2\2\2\2\u0095\3\2\2\2")
        buf.write(u"\2\u0097\3\2\2\2\2\u009b\3\2\2\2\2\u009d\3\2\2\2\2\u009f")
        buf.write(u"\3\2\2\2\2\u00a1\3\2\2\2\2\u00a3\3\2\2\2\2\u00a5\3\2")
        buf.write(u"\2\2\2\u00a7\3\2\2\2\2\u00a9\3\2\2\2\2\u00ab\3\2\2\2")
        buf.write(u"\2\u00ad\3\2\2\2\2\u00af\3\2\2\2\2\u00b1\3\2\2\2\2\u00b3")
        buf.write(u"\3\2\2\2\3\u00b5\3\2\2\2\5\u00b8\3\2\2\2\7\u00ca\3\2")
        buf.write(u"\2\2\t\u00d9\3\2\2\2\13\u00ea\3\2\2\2\r\u00ee\3\2\2\2")
        buf.write(u"\17\u00f6\3\2\2\2\21\u010e\3\2\2\2\23\u0112\3\2\2\2\25")
        buf.write(u"\u0121\3\2\2\2\27\u0132\3\2\2\2\31\u013a\3\2\2\2\33\u0176")
        buf.write(u"\3\2\2\2\35\u017a\3\2\2\2\37\u017c\3\2\2\2!\u017e\3\2")
        buf.write(u"\2\2#\u0180\3\2\2\2%\u0182\3\2\2\2\'\u0184\3\2\2\2)\u0186")
        buf.write(u"\3\2\2\2+\u0188\3\2\2\2-\u018a\3\2\2\2/\u018d\3\2\2\2")
        buf.write(u"\61\u0190\3\2\2\2\63\u0192\3\2\2\2\65\u0194\3\2\2\2\67")
        buf.write(u"\u0196\3\2\2\29\u019e\3\2\2\2;\u01a5\3\2\2\2=\u01ad\3")
        buf.write(u"\2\2\2?\u01b5\3\2\2\2A\u01f1\3\2\2\2C\u01f3\3\2\2\2E")
        buf.write(u"\u01f8\3\2\2\2G\u01fd\3\2\2\2I\u0203\3\2\2\2K\u0208\3")
        buf.write(u"\2\2\2M\u020d\3\2\2\2O\u0211\3\2\2\2Q\u0216\3\2\2\2S")
        buf.write(u"\u021b\3\2\2\2U\u0220\3\2\2\2W\u0225\3\2\2\2Y\u022a\3")
        buf.write(u"\2\2\2[\u022f\3\2\2\2]\u0237\3\2\2\2_\u023f\3\2\2\2a")
        buf.write(u"\u0247\3\2\2\2c\u024f\3\2\2\2e\u0257\3\2\2\2g\u025f\3")
        buf.write(u"\2\2\2i\u0265\3\2\2\2k\u026b\3\2\2\2m\u0271\3\2\2\2o")
        buf.write(u"\u0279\3\2\2\2q\u0281\3\2\2\2s\u0289\3\2\2\2u\u0291\3")
        buf.write(u"\2\2\2w\u0299\3\2\2\2y\u02a0\3\2\2\2{\u02a7\3\2\2\2}")
        buf.write(u"\u02ad\3\2\2\2\177\u02b4\3\2\2\2\u0081\u02ba\3\2\2\2")
        buf.write(u"\u0083\u02bf\3\2\2\2\u0085\u02c5\3\2\2\2\u0087\u02cc")
        buf.write(u"\3\2\2\2\u0089\u02d4\3\2\2\2\u008b\u02dc\3\2\2\2\u008d")
        buf.write(u"\u02e4\3\2\2\2\u008f\u02e6\3\2\2\2\u0091\u02e8\3\2\2")
        buf.write(u"\2\u0093\u02ea\3\2\2\2\u0095\u02ec\3\2\2\2\u0097\u02fc")
        buf.write(u"\3\2\2\2\u0099\u02fe\3\2\2\2\u009b\u0325\3\2\2\2\u009d")
        buf.write(u"\u033b\3\2\2\2\u009f\u033d\3\2\2\2\u00a1\u0342\3\2\2")
        buf.write(u"\2\u00a3\u034d\3\2\2\2\u00a5\u034f\3\2\2\2\u00a7\u0355")
        buf.write(u"\3\2\2\2\u00a9\u035f\3\2\2\2\u00ab\u036a\3\2\2\2\u00ad")
        buf.write(u"\u036c\3\2\2\2\u00af\u0372\3\2\2\2\u00b1\u037c\3\2\2")
        buf.write(u"\2\u00b3\u037e\3\2\2\2\u00b5\u00b6\7.\2\2\u00b6\4\3\2")
        buf.write(u"\2\2\u00b7\u00b9\t\2\2\2\u00b8\u00b7\3\2\2\2\u00b9\u00ba")
        buf.write(u"\3\2\2\2\u00ba\u00b8\3\2\2\2\u00ba\u00bb\3\2\2\2\u00bb")
        buf.write(u"\u00bc\3\2\2\2\u00bc\u00bd\b\3\2\2\u00bd\6\3\2\2\2\u00be")
        buf.write(u"\u00bf\7^\2\2\u00bf\u00cb\7.\2\2\u00c0\u00c1\7^\2\2\u00c1")
        buf.write(u"\u00c2\7v\2\2\u00c2\u00c3\7j\2\2\u00c3\u00c4\7k\2\2\u00c4")
        buf.write(u"\u00c5\7p\2\2\u00c5\u00c6\7u\2\2\u00c6\u00c7\7r\2\2\u00c7")
        buf.write(u"\u00c8\7c\2\2\u00c8\u00c9\7e\2\2\u00c9\u00cb\7g\2\2\u00ca")
        buf.write(u"\u00be\3\2\2\2\u00ca\u00c0\3\2\2\2\u00cb\u00cc\3\2\2")
        buf.write(u"\2\u00cc\u00cd\b\4\2\2\u00cd\b\3\2\2\2\u00ce\u00cf\7")
        buf.write(u"^\2\2\u00cf\u00da\7<\2\2\u00d0\u00d1\7^\2\2\u00d1\u00d2")
        buf.write(u"\7o\2\2\u00d2\u00d3\7g\2\2\u00d3\u00d4\7f\2\2\u00d4\u00d5")
        buf.write(u"\7u\2\2\u00d5\u00d6\7r\2\2\u00d6\u00d7\7c\2\2\u00d7\u00d8")
        buf.write(u"\7e\2\2\u00d8\u00da\7g\2\2\u00d9\u00ce\3\2\2\2\u00d9")
        buf.write(u"\u00d0\3\2\2\2\u00da\u00db\3\2\2\2\u00db\u00dc\b\5\2")
        buf.write(u"\2\u00dc\n\3\2\2\2\u00dd\u00de\7^\2\2\u00de\u00eb\7=")
        buf.write(u"\2\2\u00df\u00e0\7^\2\2\u00e0\u00e1\7v\2\2\u00e1\u00e2")
        buf.write(u"\7j\2\2\u00e2\u00e3\7k\2\2\u00e3\u00e4\7e\2\2\u00e4\u00e5")
        buf.write(u"\7m\2\2\u00e5\u00e6\7u\2\2\u00e6\u00e7\7r\2\2\u00e7\u00e8")
        buf.write(u"\7c\2\2\u00e8\u00e9\7e\2\2\u00e9\u00eb\7g\2\2\u00ea\u00dd")
        buf.write(u"\3\2\2\2\u00ea\u00df\3\2\2\2\u00eb\u00ec\3\2\2\2\u00ec")
        buf.write(u"\u00ed\b\6\2\2\u00ed\f\3\2\2\2\u00ee\u00ef\7^\2\2\u00ef")
        buf.write(u"\u00f0\7s\2\2\u00f0\u00f1\7w\2\2\u00f1\u00f2\7c\2\2\u00f2")
        buf.write(u"\u00f3\7f\2\2\u00f3\u00f4\3\2\2\2\u00f4\u00f5\b\7\2\2")
        buf.write(u"\u00f5\16\3\2\2\2\u00f6\u00f7\7^\2\2\u00f7\u00f8\7s\2")
        buf.write(u"\2\u00f8\u00f9\7s\2\2\u00f9\u00fa\7w\2\2\u00fa\u00fb")
        buf.write(u"\7c\2\2\u00fb\u00fc\7f\2\2\u00fc\u00fd\3\2\2\2\u00fd")
        buf.write(u"\u00fe\b\b\2\2\u00fe\20\3\2\2\2\u00ff\u0100\7^\2\2\u0100")
        buf.write(u"\u010f\7#\2\2\u0101\u0102\7^\2\2\u0102\u0103\7p\2\2\u0103")
        buf.write(u"\u0104\7g\2\2\u0104\u0105\7i\2\2\u0105\u0106\7v\2\2\u0106")
        buf.write(u"\u0107\7j\2\2\u0107\u0108\7k\2\2\u0108\u0109\7p\2\2\u0109")
        buf.write(u"\u010a\7u\2\2\u010a\u010b\7r\2\2\u010b\u010c\7c\2\2\u010c")
        buf.write(u"\u010d\7e\2\2\u010d\u010f\7g\2\2\u010e\u00ff\3\2\2\2")
        buf.write(u"\u010e\u0101\3\2\2\2\u010f\u0110\3\2\2\2\u0110\u0111")
        buf.write(u"\b\t\2\2\u0111\22\3\2\2\2\u0112\u0113\7^\2\2\u0113\u0114")
        buf.write(u"\7p\2\2\u0114\u0115\7g\2\2\u0115\u0116\7i\2\2\u0116\u0117")
        buf.write(u"\7o\2\2\u0117\u0118\7g\2\2\u0118\u0119\7f\2\2\u0119\u011a")
        buf.write(u"\7u\2\2\u011a\u011b\7r\2\2\u011b\u011c\7c\2\2\u011c\u011d")
        buf.write(u"\7e\2\2\u011d\u011e\7g\2\2\u011e\u011f\3\2\2\2\u011f")
        buf.write(u"\u0120\b\n\2\2\u0120\24\3\2\2\2\u0121\u0122\7^\2\2\u0122")
        buf.write(u"\u0123\7p\2\2\u0123\u0124\7g\2\2\u0124\u0125\7i\2\2\u0125")
        buf.write(u"\u0126\7v\2\2\u0126\u0127\7j\2\2\u0127\u0128\7k\2\2\u0128")
        buf.write(u"\u0129\7e\2\2\u0129\u012a\7m\2\2\u012a\u012b\7u\2\2\u012b")
        buf.write(u"\u012c\7r\2\2\u012c\u012d\7c\2\2\u012d\u012e\7e\2\2\u012e")
        buf.write(u"\u012f\7g\2\2\u012f\u0130\3\2\2\2\u0130\u0131\b\13\2")
        buf.write(u"\2\u0131\26\3\2\2\2\u0132\u0133\7^\2\2\u0133\u0134\7")
        buf.write(u"n\2\2\u0134\u0135\7g\2\2\u0135\u0136\7h\2\2\u0136\u0137")
        buf.write(u"\7v\2\2\u0137\u0138\3\2\2\2\u0138\u0139\b\f\2\2\u0139")
        buf.write(u"\30\3\2\2\2\u013a\u013b\7^\2\2\u013b\u013c\7t\2\2\u013c")
        buf.write(u"\u013d\7k\2\2\u013d\u013e\7i\2\2\u013e\u013f\7j\2\2\u013f")
        buf.write(u"\u0140\7v\2\2\u0140\u0141\3\2\2\2\u0141\u0142\b\r\2\2")
        buf.write(u"\u0142\32\3\2\2\2\u0143\u0144\7^\2\2\u0144\u0145\7x\2")
        buf.write(u"\2\u0145\u0146\7t\2\2\u0146\u0147\7w\2\2\u0147\u0148")
        buf.write(u"\7n\2\2\u0148\u0177\7g\2\2\u0149\u014a\7^\2\2\u014a\u014b")
        buf.write(u"\7x\2\2\u014b\u014c\7e\2\2\u014c\u014d\7g\2\2\u014d\u014e")
        buf.write(u"\7p\2\2\u014e\u014f\7v\2\2\u014f\u0150\7g\2\2\u0150\u0177")
        buf.write(u"\7t\2\2\u0151\u0152\7^\2\2\u0152\u0153\7x\2\2\u0153\u0154")
        buf.write(u"\7d\2\2\u0154\u0155\7q\2\2\u0155\u0177\7z\2\2\u0156\u0157")
        buf.write(u"\7^\2\2\u0157\u0158\7x\2\2\u0158\u0159\7u\2\2\u0159\u015a")
        buf.write(u"\7m\2\2\u015a\u015b\7k\2\2\u015b\u0177\7r\2\2\u015c\u015d")
        buf.write(u"\7^\2\2\u015d\u015e\7x\2\2\u015e\u015f\7u\2\2\u015f\u0160")
        buf.write(u"\7r\2\2\u0160\u0161\7c\2\2\u0161\u0162\7e\2\2\u0162\u0177")
        buf.write(u"\7g\2\2\u0163\u0164\7^\2\2\u0164\u0165\7j\2\2\u0165\u0166")
        buf.write(u"\7h\2\2\u0166\u0167\7k\2\2\u0167\u0177\7n\2\2\u0168\u0169")
        buf.write(u"\7^\2\2\u0169\u0177\7,\2\2\u016a\u016b\7^\2\2\u016b\u0177")
        buf.write(u"\7/\2\2\u016c\u016d\7^\2\2\u016d\u0177\7\60\2\2\u016e")
        buf.write(u"\u016f\7^\2\2\u016f\u0177\7\61\2\2\u0170\u0171\7^\2\2")
        buf.write(u"\u0171\u0177\7$\2\2\u0172\u0173\7^\2\2\u0173\u0177\7")
        buf.write(u"*\2\2\u0174\u0175\7^\2\2\u0175\u0177\7?\2\2\u0176\u0143")
        buf.write(u"\3\2\2\2\u0176\u0149\3\2\2\2\u0176\u0151\3\2\2\2\u0176")
        buf.write(u"\u0156\3\2\2\2\u0176\u015c\3\2\2\2\u0176\u0163\3\2\2")
        buf.write(u"\2\u0176\u0168\3\2\2\2\u0176\u016a\3\2\2\2\u0176\u016c")
        buf.write(u"\3\2\2\2\u0176\u016e\3\2\2\2\u0176\u0170\3\2\2\2\u0176")
        buf.write(u"\u0172\3\2\2\2\u0176\u0174\3\2\2\2\u0177\u0178\3\2\2")
        buf.write(u"\2\u0178\u0179\b\16\2\2\u0179\34\3\2\2\2\u017a\u017b")
        buf.write(u"\7-\2\2\u017b\36\3\2\2\2\u017c\u017d\7/\2\2\u017d \3")
        buf.write(u"\2\2\2\u017e\u017f\7,\2\2\u017f\"\3\2\2\2\u0180\u0181")
        buf.write(u"\7\61\2\2\u0181$\3\2\2\2\u0182\u0183\7*\2\2\u0183&\3")
        buf.write(u"\2\2\2\u0184\u0185\7+\2\2\u0185(\3\2\2\2\u0186\u0187")
        buf.write(u"\7}\2\2\u0187*\3\2\2\2\u0188\u0189\7\177\2\2\u0189,\3")
        buf.write(u"\2\2\2\u018a\u018b\7^\2\2\u018b\u018c\7}\2\2\u018c.\3")
        buf.write(u"\2\2\2\u018d\u018e\7^\2\2\u018e\u018f\7\177\2\2\u018f")
        buf.write(u"\60\3\2\2\2\u0190\u0191\7]\2\2\u0191\62\3\2\2\2\u0192")
        buf.write(u"\u0193\7_\2\2\u0193\64\3\2\2\2\u0194\u0195\7~\2\2\u0195")
        buf.write(u"\66\3\2\2\2\u0196\u0197\7^\2\2\u0197\u0198\7t\2\2\u0198")
        buf.write(u"\u0199\7k\2\2\u0199\u019a\7i\2\2\u019a\u019b\7j\2\2\u019b")
        buf.write(u"\u019c\7v\2\2\u019c\u019d\7~\2\2\u019d8\3\2\2\2\u019e")
        buf.write(u"\u019f\7^\2\2\u019f\u01a0\7n\2\2\u01a0\u01a1\7g\2\2\u01a1")
        buf.write(u"\u01a2\7h\2\2\u01a2\u01a3\7v\2\2\u01a3\u01a4\7~\2\2\u01a4")
        buf.write(u":\3\2\2\2\u01a5\u01a6\7^\2\2\u01a6\u01a7\7n\2\2\u01a7")
        buf.write(u"\u01a8\7c\2\2\u01a8\u01a9\7p\2\2\u01a9\u01aa\7i\2\2\u01aa")
        buf.write(u"\u01ab\7n\2\2\u01ab\u01ac\7g\2\2\u01ac<\3\2\2\2\u01ad")
        buf.write(u"\u01ae\7^\2\2\u01ae\u01af\7t\2\2\u01af\u01b0\7c\2\2\u01b0")
        buf.write(u"\u01b1\7p\2\2\u01b1\u01b2\7i\2\2\u01b2\u01b3\7n\2\2\u01b3")
        buf.write(u"\u01b4\7g\2\2\u01b4>\3\2\2\2\u01b5\u01b6\7^\2\2\u01b6")
        buf.write(u"\u01b7\7n\2\2\u01b7\u01b8\7k\2\2\u01b8\u01b9\7o\2\2\u01b9")
        buf.write(u"@\3\2\2\2\u01ba\u01bb\7^\2\2\u01bb\u01bc\7v\2\2\u01bc")
        buf.write(u"\u01f2\7q\2\2\u01bd\u01be\7^\2\2\u01be\u01bf\7t\2\2\u01bf")
        buf.write(u"\u01c0\7k\2\2\u01c0\u01c1\7i\2\2\u01c1\u01c2\7j\2\2\u01c2")
        buf.write(u"\u01c3\7v\2\2\u01c3\u01c4\7c\2\2\u01c4\u01c5\7t\2\2\u01c5")
        buf.write(u"\u01c6\7t\2\2\u01c6\u01c7\7q\2\2\u01c7\u01f2\7y\2\2\u01c8")
        buf.write(u"\u01c9\7^\2\2\u01c9\u01ca\7T\2\2\u01ca\u01cb\7k\2\2\u01cb")
        buf.write(u"\u01cc\7i\2\2\u01cc\u01cd\7j\2\2\u01cd\u01ce\7v\2\2\u01ce")
        buf.write(u"\u01cf\7c\2\2\u01cf\u01d0\7t\2\2\u01d0\u01d1\7t\2\2\u01d1")
        buf.write(u"\u01d2\7q\2\2\u01d2\u01f2\7y\2\2\u01d3\u01d4\7^\2\2\u01d4")
        buf.write(u"\u01d5\7n\2\2\u01d5\u01d6\7q\2\2\u01d6\u01d7\7p\2\2\u01d7")
        buf.write(u"\u01d8\7i\2\2\u01d8\u01d9\7t\2\2\u01d9\u01da\7k\2\2\u01da")
        buf.write(u"\u01db\7i\2\2\u01db\u01dc\7j\2\2\u01dc\u01dd\7v\2\2\u01dd")
        buf.write(u"\u01de\7c\2\2\u01de\u01df\7t\2\2\u01df\u01e0\7t\2\2\u01e0")
        buf.write(u"\u01e1\7q\2\2\u01e1\u01f2\7y\2\2\u01e2\u01e3\7^\2\2\u01e3")
        buf.write(u"\u01e4\7N\2\2\u01e4\u01e5\7q\2\2\u01e5\u01e6\7p\2\2\u01e6")
        buf.write(u"\u01e7\7i\2\2\u01e7\u01e8\7t\2\2\u01e8\u01e9\7k\2\2\u01e9")
        buf.write(u"\u01ea\7i\2\2\u01ea\u01eb\7j\2\2\u01eb\u01ec\7v\2\2\u01ec")
        buf.write(u"\u01ed\7c\2\2\u01ed\u01ee\7t\2\2\u01ee\u01ef\7t\2\2\u01ef")
        buf.write(u"\u01f0\7q\2\2\u01f0\u01f2\7y\2\2\u01f1\u01ba\3\2\2\2")
        buf.write(u"\u01f1\u01bd\3\2\2\2\u01f1\u01c8\3\2\2\2\u01f1\u01d3")
        buf.write(u"\3\2\2\2\u01f1\u01e2\3\2\2\2\u01f2B\3\2\2\2\u01f3\u01f4")
        buf.write(u"\7^\2\2\u01f4\u01f5\7k\2\2\u01f5\u01f6\7p\2\2\u01f6\u01f7")
        buf.write(u"\7v\2\2\u01f7D\3\2\2\2\u01f8\u01f9\7^\2\2\u01f9\u01fa")
        buf.write(u"\7u\2\2\u01fa\u01fb\7w\2\2\u01fb\u01fc\7o\2\2\u01fcF")
        buf.write(u"\3\2\2\2\u01fd\u01fe\7^\2\2\u01fe\u01ff\7r\2\2\u01ff")
        buf.write(u"\u0200\7t\2\2\u0200\u0201\7q\2\2\u0201\u0202\7f\2\2\u0202")
        buf.write(u"H\3\2\2\2\u0203\u0204\7^\2\2\u0204\u0205\7g\2\2\u0205")
        buf.write(u"\u0206\7z\2\2\u0206\u0207\7r\2\2\u0207J\3\2\2\2\u0208")
        buf.write(u"\u0209\7^\2\2\u0209\u020a\7n\2\2\u020a\u020b\7q\2\2\u020b")
        buf.write(u"\u020c\7i\2\2\u020cL\3\2\2\2\u020d\u020e\7^\2\2\u020e")
        buf.write(u"\u020f\7n\2\2\u020f\u0210\7p\2\2\u0210N\3\2\2\2\u0211")
        buf.write(u"\u0212\7^\2\2\u0212\u0213\7u\2\2\u0213\u0214\7k\2\2\u0214")
        buf.write(u"\u0215\7p\2\2\u0215P\3\2\2\2\u0216\u0217\7^\2\2\u0217")
        buf.write(u"\u0218\7e\2\2\u0218\u0219\7q\2\2\u0219\u021a\7u\2\2\u021a")
        buf.write(u"R\3\2\2\2\u021b\u021c\7^\2\2\u021c\u021d\7v\2\2\u021d")
        buf.write(u"\u021e\7c\2\2\u021e\u021f\7p\2\2\u021fT\3\2\2\2\u0220")
        buf.write(u"\u0221\7^\2\2\u0221\u0222\7e\2\2\u0222\u0223\7u\2\2\u0223")
        buf.write(u"\u0224\7e\2\2\u0224V\3\2\2\2\u0225\u0226\7^\2\2\u0226")
        buf.write(u"\u0227\7u\2\2\u0227\u0228\7g\2\2\u0228\u0229\7e\2\2\u0229")
        buf.write(u"X\3\2\2\2\u022a\u022b\7^\2\2\u022b\u022c\7e\2\2\u022c")
        buf.write(u"\u022d\7q\2\2\u022d\u022e\7v\2\2\u022eZ\3\2\2\2\u022f")
        buf.write(u"\u0230\7^\2\2\u0230\u0231\7c\2\2\u0231\u0232\7t\2\2\u0232")
        buf.write(u"\u0233\7e\2\2\u0233\u0234\7u\2\2\u0234\u0235\7k\2\2\u0235")
        buf.write(u"\u0236\7p\2\2\u0236\\\3\2\2\2\u0237\u0238\7^\2\2\u0238")
        buf.write(u"\u0239\7c\2\2\u0239\u023a\7t\2\2\u023a\u023b\7e\2\2\u023b")
        buf.write(u"\u023c\7e\2\2\u023c\u023d\7q\2\2\u023d\u023e\7u\2\2\u023e")
        buf.write(u"^\3\2\2\2\u023f\u0240\7^\2\2\u0240\u0241\7c\2\2\u0241")
        buf.write(u"\u0242\7t\2\2\u0242\u0243\7e\2\2\u0243\u0244\7v\2\2\u0244")
        buf.write(u"\u0245\7c\2\2\u0245\u0246\7p\2\2\u0246`\3\2\2\2\u0247")
        buf.write(u"\u0248\7^\2\2\u0248\u0249\7c\2\2\u0249\u024a\7t\2\2\u024a")
        buf.write(u"\u024b\7e\2\2\u024b\u024c\7e\2\2\u024c\u024d\7u\2\2\u024d")
        buf.write(u"\u024e\7e\2\2\u024eb\3\2\2\2\u024f\u0250\7^\2\2\u0250")
        buf.write(u"\u0251\7c\2\2\u0251\u0252\7t\2\2\u0252\u0253\7e\2\2\u0253")
        buf.write(u"\u0254\7u\2\2\u0254\u0255\7g\2\2\u0255\u0256\7e\2\2\u0256")
        buf.write(u"d\3\2\2\2\u0257\u0258\7^\2\2\u0258\u0259\7c\2\2\u0259")
        buf.write(u"\u025a\7t\2\2\u025a\u025b\7e\2\2\u025b\u025c\7e\2\2\u025c")
        buf.write(u"\u025d\7q\2\2\u025d\u025e\7v\2\2\u025ef\3\2\2\2\u025f")
        buf.write(u"\u0260\7^\2\2\u0260\u0261\7u\2\2\u0261\u0262\7k\2\2\u0262")
        buf.write(u"\u0263\7p\2\2\u0263\u0264\7j\2\2\u0264h\3\2\2\2\u0265")
        buf.write(u"\u0266\7^\2\2\u0266\u0267\7e\2\2\u0267\u0268\7q\2\2\u0268")
        buf.write(u"\u0269\7u\2\2\u0269\u026a\7j\2\2\u026aj\3\2\2\2\u026b")
        buf.write(u"\u026c\7^\2\2\u026c\u026d\7v\2\2\u026d\u026e\7c\2\2\u026e")
        buf.write(u"\u026f\7p\2\2\u026f\u0270\7j\2\2\u0270l\3\2\2\2\u0271")
        buf.write(u"\u0272\7^\2\2\u0272\u0273\7c\2\2\u0273\u0274\7t\2\2\u0274")
        buf.write(u"\u0275\7u\2\2\u0275\u0276\7k\2\2\u0276\u0277\7p\2\2\u0277")
        buf.write(u"\u0278\7j\2\2\u0278n\3\2\2\2\u0279\u027a\7^\2\2\u027a")
        buf.write(u"\u027b\7c\2\2\u027b\u027c\7t\2\2\u027c\u027d\7e\2\2\u027d")
        buf.write(u"\u027e\7q\2\2\u027e\u027f\7u\2\2\u027f\u0280\7j\2\2\u0280")
        buf.write(u"p\3\2\2\2\u0281\u0282\7^\2\2\u0282\u0283\7c\2\2\u0283")
        buf.write(u"\u0284\7t\2\2\u0284\u0285\7v\2\2\u0285\u0286\7c\2\2\u0286")
        buf.write(u"\u0287\7p\2\2\u0287\u0288\7j\2\2\u0288r\3\2\2\2\u0289")
        buf.write(u"\u028a\7^\2\2\u028a\u028b\7n\2\2\u028b\u028c\7h\2\2\u028c")
        buf.write(u"\u028d\7n\2\2\u028d\u028e\7q\2\2\u028e\u028f\7q\2\2\u028f")
        buf.write(u"\u0290\7t\2\2\u0290t\3\2\2\2\u0291\u0292\7^\2\2\u0292")
        buf.write(u"\u0293\7t\2\2\u0293\u0294\7h\2\2\u0294\u0295\7n\2\2\u0295")
        buf.write(u"\u0296\7q\2\2\u0296\u0297\7q\2\2\u0297\u0298\7t\2\2\u0298")
        buf.write(u"v\3\2\2\2\u0299\u029a\7^\2\2\u029a\u029b\7n\2\2\u029b")
        buf.write(u"\u029c\7e\2\2\u029c\u029d\7g\2\2\u029d\u029e\7k\2\2\u029e")
        buf.write(u"\u029f\7n\2\2\u029fx\3\2\2\2\u02a0\u02a1\7^\2\2\u02a1")
        buf.write(u"\u02a2\7t\2\2\u02a2\u02a3\7e\2\2\u02a3\u02a4\7g\2\2\u02a4")
        buf.write(u"\u02a5\7k\2\2\u02a5\u02a6\7n\2\2\u02a6z\3\2\2\2\u02a7")
        buf.write(u"\u02a8\7^\2\2\u02a8\u02a9\7u\2\2\u02a9\u02aa\7s\2\2\u02aa")
        buf.write(u"\u02ab\7t\2\2\u02ab\u02ac\7v\2\2\u02ac|\3\2\2\2\u02ad")
        buf.write(u"\u02ae\7^\2\2\u02ae\u02af\7v\2\2\u02af\u02b0\7k\2\2\u02b0")
        buf.write(u"\u02b1\7o\2\2\u02b1\u02b2\7g\2\2\u02b2\u02b3\7u\2\2\u02b3")
        buf.write(u"~\3\2\2\2\u02b4\u02b5\7^\2\2\u02b5\u02b6\7e\2\2\u02b6")
        buf.write(u"\u02b7\7f\2\2\u02b7\u02b8\7q\2\2\u02b8\u02b9\7v\2\2\u02b9")
        buf.write(u"\u0080\3\2\2\2\u02ba\u02bb\7^\2\2\u02bb\u02bc\7f\2\2")
        buf.write(u"\u02bc\u02bd\7k\2\2\u02bd\u02be\7x\2\2\u02be\u0082\3")
        buf.write(u"\2\2\2\u02bf\u02c0\7^\2\2\u02c0\u02c1\7h\2\2\u02c1\u02c2")
        buf.write(u"\7t\2\2\u02c2\u02c3\7c\2\2\u02c3\u02c4\7e\2\2\u02c4\u0084")
        buf.write(u"\3\2\2\2\u02c5\u02c6\7^\2\2\u02c6\u02c7\7d\2\2\u02c7")
        buf.write(u"\u02c8\7k\2\2\u02c8\u02c9\7p\2\2\u02c9\u02ca\7q\2\2\u02ca")
        buf.write(u"\u02cb\7o\2\2\u02cb\u0086\3\2\2\2\u02cc\u02cd\7^\2\2")
        buf.write(u"\u02cd\u02ce\7f\2\2\u02ce\u02cf\7d\2\2\u02cf\u02d0\7")
        buf.write(u"k\2\2\u02d0\u02d1\7p\2\2\u02d1\u02d2\7q\2\2\u02d2\u02d3")
        buf.write(u"\7o\2\2\u02d3\u0088\3\2\2\2\u02d4\u02d5\7^\2\2\u02d5")
        buf.write(u"\u02d6\7v\2\2\u02d6\u02d7\7d\2\2\u02d7\u02d8\7k\2\2\u02d8")
        buf.write(u"\u02d9\7p\2\2\u02d9\u02da\7q\2\2\u02da\u02db\7o\2\2\u02db")
        buf.write(u"\u008a\3\2\2\2\u02dc\u02dd\7^\2\2\u02dd\u02de\7o\2\2")
        buf.write(u"\u02de\u02df\7c\2\2\u02df\u02e0\7v\2\2\u02e0\u02e1\7")
        buf.write(u"j\2\2\u02e1\u02e2\7k\2\2\u02e2\u02e3\7v\2\2\u02e3\u008c")
        buf.write(u"\3\2\2\2\u02e4\u02e5\7a\2\2\u02e5\u008e\3\2\2\2\u02e6")
        buf.write(u"\u02e7\7`\2\2\u02e7\u0090\3\2\2\2\u02e8\u02e9\7<\2\2")
        buf.write(u"\u02e9\u0092\3\2\2\2\u02ea\u02eb\t\2\2\2\u02eb\u0094")
        buf.write(u"\3\2\2\2\u02ec\u02f0\7f\2\2\u02ed\u02ef\5\u0093J\2\u02ee")
        buf.write(u"\u02ed\3\2\2\2\u02ef\u02f2\3\2\2\2\u02f0\u02f1\3\2\2")
        buf.write(u"\2\u02f0\u02ee\3\2\2\2\u02f1\u02fa\3\2\2\2\u02f2\u02f0")
        buf.write(u"\3\2\2\2\u02f3\u02fb\t\3\2\2\u02f4\u02f6\7^\2\2\u02f5")
        buf.write(u"\u02f7\t\3\2\2\u02f6\u02f5\3\2\2\2\u02f7\u02f8\3\2\2")
        buf.write(u"\2\u02f8\u02f6\3\2\2\2\u02f8\u02f9\3\2\2\2\u02f9\u02fb")
        buf.write(u"\3\2\2\2\u02fa\u02f3\3\2\2\2\u02fa\u02f4\3\2\2\2\u02fb")
        buf.write(u"\u0096\3\2\2\2\u02fc\u02fd\t\3\2\2\u02fd\u0098\3\2\2")
        buf.write(u"\2\u02fe\u02ff\t\4\2\2\u02ff\u009a\3\2\2\2\u0300\u0302")
        buf.write(u"\5\u0099M\2\u0301\u0300\3\2\2\2\u0302\u0303\3\2\2\2\u0303")
        buf.write(u"\u0301\3\2\2\2\u0303\u0304\3\2\2\2\u0304\u030c\3\2\2")
        buf.write(u"\2\u0305\u0306\7.\2\2\u0306\u0307\5\u0099M\2\u0307\u0308")
        buf.write(u"\5\u0099M\2\u0308\u0309\5\u0099M\2\u0309\u030b\3\2\2")
        buf.write(u"\2\u030a\u0305\3\2\2\2\u030b\u030e\3\2\2\2\u030c\u030a")
        buf.write(u"\3\2\2\2\u030c\u030d\3\2\2\2\u030d\u0326\3\2\2\2\u030e")
        buf.write(u"\u030c\3\2\2\2\u030f\u0311\5\u0099M\2\u0310\u030f\3\2")
        buf.write(u"\2\2\u0311\u0314\3\2\2\2\u0312\u0310\3\2\2\2\u0312\u0313")
        buf.write(u"\3\2\2\2\u0313\u031c\3\2\2\2\u0314\u0312\3\2\2\2\u0315")
        buf.write(u"\u0316\7.\2\2\u0316\u0317\5\u0099M\2\u0317\u0318\5\u0099")
        buf.write(u"M\2\u0318\u0319\5\u0099M\2\u0319\u031b\3\2\2\2\u031a")
        buf.write(u"\u0315\3\2\2\2\u031b\u031e\3\2\2\2\u031c\u031a\3\2\2")
        buf.write(u"\2\u031c\u031d\3\2\2\2\u031d\u031f\3\2\2\2\u031e\u031c")
        buf.write(u"\3\2\2\2\u031f\u0321\7\60\2\2\u0320\u0322\5\u0099M\2")
        buf.write(u"\u0321\u0320\3\2\2\2\u0322\u0323\3\2\2\2\u0323\u0321")
        buf.write(u"\3\2\2\2\u0323\u0324\3\2\2\2\u0324\u0326\3\2\2\2\u0325")
        buf.write(u"\u0301\3\2\2\2\u0325\u0312\3\2\2\2\u0326\u009c\3\2\2")
        buf.write(u"\2\u0327\u032b\7(\2\2\u0328\u032a\5\u0093J\2\u0329\u0328")
        buf.write(u"\3\2\2\2\u032a\u032d\3\2\2\2\u032b\u032c\3\2\2\2\u032b")
        buf.write(u"\u0329\3\2\2\2\u032c\u032f\3\2\2\2\u032d\u032b\3\2\2")
        buf.write(u"\2\u032e\u0327\3\2\2\2\u032e\u032f\3\2\2\2\u032f\u0330")
        buf.write(u"\3\2\2\2\u0330\u033c\7?\2\2\u0331\u0339\7?\2\2\u0332")
        buf.write(u"\u0334\5\u0093J\2\u0333\u0332\3\2\2\2\u0334\u0337\3\2")
        buf.write(u"\2\2\u0335\u0336\3\2\2\2\u0335\u0333\3\2\2\2\u0336\u0338")
        buf.write(u"\3\2\2\2\u0337\u0335\3\2\2\2\u0338\u033a\7(\2\2\u0339")
        buf.write(u"\u0335\3\2\2\2\u0339\u033a\3\2\2\2\u033a\u033c\3\2\2")
        buf.write(u"\2\u033b\u032e\3\2\2\2\u033b\u0331\3\2\2\2\u033c\u009e")
        buf.write(u"\3\2\2\2\u033d\u033e\7^\2\2\u033e\u033f\7p\2\2\u033f")
        buf.write(u"\u0340\7g\2\2\u0340\u0341\7s\2\2\u0341\u00a0\3\2\2\2")
        buf.write(u"\u0342\u0343\7>\2\2\u0343\u00a2\3\2\2\2\u0344\u0345\7")
        buf.write(u"^\2\2\u0345\u0346\7n\2\2\u0346\u0347\7g\2\2\u0347\u034e")
        buf.write(u"\7s\2\2\u0348\u0349\7^\2\2\u0349\u034a\7n\2\2\u034a\u034e")
        buf.write(u"\7g\2\2\u034b\u034e\5\u00a5S\2\u034c\u034e\5\u00a7T\2")
        buf.write(u"\u034d\u0344\3\2\2\2\u034d\u0348\3\2\2\2\u034d\u034b")
        buf.write(u"\3\2\2\2\u034d\u034c\3\2\2\2\u034e\u00a4\3\2\2\2\u034f")
        buf.write(u"\u0350\7^\2\2\u0350\u0351\7n\2\2\u0351\u0352\7g\2\2\u0352")
        buf.write(u"\u0353\7s\2\2\u0353\u0354\7s\2\2\u0354\u00a6\3\2\2\2")
        buf.write(u"\u0355\u0356\7^\2\2\u0356\u0357\7n\2\2\u0357\u0358\7")
        buf.write(u"g\2\2\u0358\u0359\7s\2\2\u0359\u035a\7u\2\2\u035a\u035b")
        buf.write(u"\7n\2\2\u035b\u035c\7c\2\2\u035c\u035d\7p\2\2\u035d\u035e")
        buf.write(u"\7v\2\2\u035e\u00a8\3\2\2\2\u035f\u0360\7@\2\2\u0360")
        buf.write(u"\u00aa\3\2\2\2\u0361\u0362\7^\2\2\u0362\u0363\7i\2\2")
        buf.write(u"\u0363\u0364\7g\2\2\u0364\u036b\7s\2\2\u0365\u0366\7")
        buf.write(u"^\2\2\u0366\u0367\7i\2\2\u0367\u036b\7g\2\2\u0368\u036b")
        buf.write(u"\5\u00adW\2\u0369\u036b\5\u00afX\2\u036a\u0361\3\2\2")
        buf.write(u"\2\u036a\u0365\3\2\2\2\u036a\u0368\3\2\2\2\u036a\u0369")
        buf.write(u"\3\2\2\2\u036b\u00ac\3\2\2\2\u036c\u036d\7^\2\2\u036d")
        buf.write(u"\u036e\7i\2\2\u036e\u036f\7g\2\2\u036f\u0370\7s\2\2\u0370")
        buf.write(u"\u0371\7s\2\2\u0371\u00ae\3\2\2\2\u0372\u0373\7^\2\2")
        buf.write(u"\u0373\u0374\7i\2\2\u0374\u0375\7g\2\2\u0375\u0376\7")
        buf.write(u"s\2\2\u0376\u0377\7u\2\2\u0377\u0378\7n\2\2\u0378\u0379")
        buf.write(u"\7c\2\2\u0379\u037a\7p\2\2\u037a\u037b\7v\2\2\u037b\u00b0")
        buf.write(u"\3\2\2\2\u037c\u037d\7#\2\2\u037d\u00b2\3\2\2\2\u037e")
        buf.write(u"\u0380\7^\2\2\u037f\u0381\t\3\2\2\u0380\u037f\3\2\2\2")
        buf.write(u"\u0381\u0382\3\2\2\2\u0382\u0380\3\2\2\2\u0382\u0383")
        buf.write(u"\3\2\2\2\u0383\u00b4\3\2\2\2\33\2\u00ba\u00ca\u00d9\u00ea")
        buf.write(u"\u010e\u0176\u01f1\u02f0\u02f8\u02fa\u0303\u030c\u0312")
        buf.write(u"\u031c\u0323\u0325\u032b\u032e\u0335\u0339\u033b\u034d")
        buf.write(u"\u036a\u0382\3\b\2\2")
        return buf.getvalue()


class LaTeXLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    T__0 = 1
    WS = 2
    THINSPACE = 3
    MEDSPACE = 4
    THICKSPACE = 5
    QUAD = 6
    QQUAD = 7
    NEGTHINSPACE = 8
    NEGMEDSPACE = 9
    NEGTHICKSPACE = 10
    CMD_LEFT = 11
    CMD_RIGHT = 12
    IGNORE = 13
    ADD = 14
    SUB = 15
    MUL = 16
    DIV = 17
    L_PAREN = 18
    R_PAREN = 19
    L_BRACE = 20
    R_BRACE = 21
    L_BRACE_LITERAL = 22
    R_BRACE_LITERAL = 23
    L_BRACKET = 24
    R_BRACKET = 25
    BAR = 26
    R_BAR = 27
    L_BAR = 28
    L_ANGLE = 29
    R_ANGLE = 30
    FUNC_LIM = 31
    LIM_APPROACH_SYM = 32
    FUNC_INT = 33
    FUNC_SUM = 34
    FUNC_PROD = 35
    FUNC_EXP = 36
    FUNC_LOG = 37
    FUNC_LN = 38
    FUNC_SIN = 39
    FUNC_COS = 40
    FUNC_TAN = 41
    FUNC_CSC = 42
    FUNC_SEC = 43
    FUNC_COT = 44
    FUNC_ARCSIN = 45
    FUNC_ARCCOS = 46
    FUNC_ARCTAN = 47
    FUNC_ARCCSC = 48
    FUNC_ARCSEC = 49
    FUNC_ARCCOT = 50
    FUNC_SINH = 51
    FUNC_COSH = 52
    FUNC_TANH = 53
    FUNC_ARSINH = 54
    FUNC_ARCOSH = 55
    FUNC_ARTANH = 56
    L_FLOOR = 57
    R_FLOOR = 58
    L_CEIL = 59
    R_CEIL = 60
    FUNC_SQRT = 61
    CMD_TIMES = 62
    CMD_CDOT = 63
    CMD_DIV = 64
    CMD_FRAC = 65
    CMD_BINOM = 66
    CMD_DBINOM = 67
    CMD_TBINOM = 68
    CMD_MATHIT = 69
    UNDERSCORE = 70
    CARET = 71
    COLON = 72
    DIFFERENTIAL = 73
    LETTER = 74
    NUMBER = 75
    EQUAL = 76
    NEQ = 77
    LT = 78
    LTE = 79
    LTE_Q = 80
    LTE_S = 81
    GT = 82
    GTE = 83
    GTE_Q = 84
    GTE_S = 85
    BANG = 86
    SYMBOL = 87

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ u"DEFAULT_MODE" ]

    literalNames = [ u"<INVALID>",
            u"','", u"'\\quad'", u"'\\qquad'", u"'\\negmedspace'", u"'\\negthickspace'",
            u"'\\left'", u"'\\right'", u"'+'", u"'-'", u"'*'", u"'/'", u"'('",
            u"')'", u"'{'", u"'}'", u"'\\{'", u"'\\}'", u"'['", u"']'",
            u"'|'", u"'\\right|'", u"'\\left|'", u"'\\langle'", u"'\\rangle'",
            u"'\\lim'", u"'\\int'", u"'\\sum'", u"'\\prod'", u"'\\exp'",
            u"'\\log'", u"'\\ln'", u"'\\sin'", u"'\\cos'", u"'\\tan'", u"'\\csc'",
            u"'\\sec'", u"'\\cot'", u"'\\arcsin'", u"'\\arccos'", u"'\\arctan'",
            u"'\\arccsc'", u"'\\arcsec'", u"'\\arccot'", u"'\\sinh'", u"'\\cosh'",
            u"'\\tanh'", u"'\\arsinh'", u"'\\arcosh'", u"'\\artanh'", u"'\\lfloor'",
            u"'\\rfloor'", u"'\\lceil'", u"'\\rceil'", u"'\\sqrt'", u"'\\times'",
            u"'\\cdot'", u"'\\div'", u"'\\frac'", u"'\\binom'", u"'\\dbinom'",
            u"'\\tbinom'", u"'\\mathit'", u"'_'", u"'^'", u"':'", u"'\\neq'",
            u"'<'", u"'\\leqq'", u"'\\leqslant'", u"'>'", u"'\\geqq'", u"'\\geqslant'",
            u"'!'" ]

    symbolicNames = [ u"<INVALID>",
            u"WS", u"THINSPACE", u"MEDSPACE", u"THICKSPACE", u"QUAD", u"QQUAD",
            u"NEGTHINSPACE", u"NEGMEDSPACE", u"NEGTHICKSPACE", u"CMD_LEFT",
            u"CMD_RIGHT", u"IGNORE", u"ADD", u"SUB", u"MUL", u"DIV", u"L_PAREN",
            u"R_PAREN", u"L_BRACE", u"R_BRACE", u"L_BRACE_LITERAL", u"R_BRACE_LITERAL",
            u"L_BRACKET", u"R_BRACKET", u"BAR", u"R_BAR", u"L_BAR", u"L_ANGLE",
            u"R_ANGLE", u"FUNC_LIM", u"LIM_APPROACH_SYM", u"FUNC_INT", u"FUNC_SUM",
            u"FUNC_PROD", u"FUNC_EXP", u"FUNC_LOG", u"FUNC_LN", u"FUNC_SIN",
            u"FUNC_COS", u"FUNC_TAN", u"FUNC_CSC", u"FUNC_SEC", u"FUNC_COT",
            u"FUNC_ARCSIN", u"FUNC_ARCCOS", u"FUNC_ARCTAN", u"FUNC_ARCCSC",
            u"FUNC_ARCSEC", u"FUNC_ARCCOT", u"FUNC_SINH", u"FUNC_COSH",
            u"FUNC_TANH", u"FUNC_ARSINH", u"FUNC_ARCOSH", u"FUNC_ARTANH",
            u"L_FLOOR", u"R_FLOOR", u"L_CEIL", u"R_CEIL", u"FUNC_SQRT",
            u"CMD_TIMES", u"CMD_CDOT", u"CMD_DIV", u"CMD_FRAC", u"CMD_BINOM",
            u"CMD_DBINOM", u"CMD_TBINOM", u"CMD_MATHIT", u"UNDERSCORE",
            u"CARET", u"COLON", u"DIFFERENTIAL", u"LETTER", u"NUMBER", u"EQUAL",
            u"NEQ", u"LT", u"LTE", u"LTE_Q", u"LTE_S", u"GT", u"GTE", u"GTE_Q",
            u"GTE_S", u"BANG", u"SYMBOL" ]

    ruleNames = [ u"T__0", u"WS", u"THINSPACE", u"MEDSPACE", u"THICKSPACE",
                  u"QUAD", u"QQUAD", u"NEGTHINSPACE", u"NEGMEDSPACE", u"NEGTHICKSPACE",
                  u"CMD_LEFT", u"CMD_RIGHT", u"IGNORE", u"ADD", u"SUB",
                  u"MUL", u"DIV", u"L_PAREN", u"R_PAREN", u"L_BRACE", u"R_BRACE",
                  u"L_BRACE_LITERAL", u"R_BRACE_LITERAL", u"L_BRACKET",
                  u"R_BRACKET", u"BAR", u"R_BAR", u"L_BAR", u"L_ANGLE",
                  u"R_ANGLE", u"FUNC_LIM", u"LIM_APPROACH_SYM", u"FUNC_INT",
                  u"FUNC_SUM", u"FUNC_PROD", u"FUNC_EXP", u"FUNC_LOG", u"FUNC_LN",
                  u"FUNC_SIN", u"FUNC_COS", u"FUNC_TAN", u"FUNC_CSC", u"FUNC_SEC",
                  u"FUNC_COT", u"FUNC_ARCSIN", u"FUNC_ARCCOS", u"FUNC_ARCTAN",
                  u"FUNC_ARCCSC", u"FUNC_ARCSEC", u"FUNC_ARCCOT", u"FUNC_SINH",
                  u"FUNC_COSH", u"FUNC_TANH", u"FUNC_ARSINH", u"FUNC_ARCOSH",
                  u"FUNC_ARTANH", u"L_FLOOR", u"R_FLOOR", u"L_CEIL", u"R_CEIL",
                  u"FUNC_SQRT", u"CMD_TIMES", u"CMD_CDOT", u"CMD_DIV", u"CMD_FRAC",
                  u"CMD_BINOM", u"CMD_DBINOM", u"CMD_TBINOM", u"CMD_MATHIT",
                  u"UNDERSCORE", u"CARET", u"COLON", u"WS_CHAR", u"DIFFERENTIAL",
                  u"LETTER", u"DIGIT", u"NUMBER", u"EQUAL", u"NEQ", u"LT",
                  u"LTE", u"LTE_Q", u"LTE_S", u"GT", u"GTE", u"GTE_Q", u"GTE_S",
                  u"BANG", u"SYMBOL" ]

    grammarFileName = u"LaTeX.g4"

    def __init__(self, input=None, output=sys.stdout):
        super(LaTeXLexer, self).__init__(input, output=output)
        self.checkVersion("4.7.2")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None

