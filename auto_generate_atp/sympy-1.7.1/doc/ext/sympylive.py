"""
    sympylive
    ~~~~~~~~~

    Allow `SymPy Live <https://live.sympy.org/>`_ to be used for interactive
    evaluation of SymPy's code examples.

    :copyright: Copyright 2014 by the SymPy Development Team, see AUTHORS.
    :license: BSD, see LICENSE for details.
"""


def builder_inited(app):
    if not app.config.sympylive_url:
        raise ExtensionError('sympylive_url config value must be set'
                             ' for the sympylive extension to work')

    app.add_js_file(app.config.sympylive_url + '/static/utilities.js')
    app.add_js_file(app.config.sympylive_url + '/static/external/classy.js')

    app.add_css_file(app.config.sympylive_url + '/static/live-core.css')
    app.add_css_file(app.config.sympylive_url +
                     '/static/live-autocomplete.css')
    app.add_css_file(app.config.sympylive_url + '/static/live-sphinx.css')

    app.add_js_file(app.config.sympylive_url + '/static/live-core.js')
    app.add_js_file(app.config.sympylive_url + '/static/live-autocomplete.js')
    app.add_js_file(app.config.sympylive_url + '/static/live-sphinx.js')


def setup(app):
    app.add_config_value('sympylive_url', 'https://live.sympy.org', False)
    app.connect('builder-inited', builder_inited)
