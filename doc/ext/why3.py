def setup(app):
    app.add_object_type('why3-transform', 'why3-transform', 'pair: %s; transformation')
    app.add_crossref_type('why3-tool', 'why3-tool', 'pair: %s; tool')

    return {
        'version': '0.1',
        'parallel_read_safe': True,
        'parallel_write_safe': True,
    }
