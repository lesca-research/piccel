
from collections import OrderedDict
import pandas as pd
from datetime import datetime

import weasyprint # TODO as dep
import PyPDF2 # TODO as dep
from io import BytesIO

def main(user, access_pwd, role_pwd):

    HTML_TOP = '''
    <html>
    <head>
    <style>
      @page {
      size: 200mm 400mm landscape;
      }
      h2 {
        text-align: center;
        font-family: Helvetica, Arial, sans-serif;
      }
      table {
        margin-left: auto;
        margin-right: auto;
      }
      table, th, td {
        border: 1px solid black;
        border-collapse: collapse;
      }
      th, td {
        padding: 5px;
        text-align: center;
        font-family: Helvetica, Arial, sans-serif;
        font-size: 90%;
      }
      table tbody tr:hover {
        background-color: #dddddd;
      }
      .wide {
        width: 90%;
      }
    </style>
    </head>
    <body>
    '''

    HTML_BOTTOM = '''
    </body>
    </html>
    '''
    df = pd.DataFrame(OrderedDict([
            ('Participant_ID', ['CE0004', 'CE0005', 'CE0006']),
            ('Referencing', ['epic_member', 'epic_member', 'epic_member']),
            ('First_Name', ['John', 'Ella', '']),
            ('Last_Name', ['McLain', 'Pissai', 'Vance']),
            ('Email_Address', ['20100thomas@gmail.com',
                               '20100thomas@gmail.com',
                               '20100thomas@gmail.com']),
            ('Phone_Number', ['000-000-0000', '514-000-0000',
                              '456-123-4565#1']),
            ('Age', [44, 34, 21]),
            ('Weight_kg', [44.7, 50.2, 70]),
            ('Entry_ts', [datetime(2013,4,5,10,10),
                          datetime(2017,11,25,15,10),
                          datetime(2014,9,5,14,16)]),
            ('Comment', ['something', 'fishy', 'around here']),
            ('exclude', [False, False, False]),
            ('Secure_ID', ['aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa',
                           '22222222222222222222222222222222',
                           '11111111111111111111111111111111']),
            ('Agree_contact', [False, True, False]),
            ('Agree_participation', [False, True, False])
        ]))
    df_html = HTML_TOP + df.to_html(classes='wide', escape=False) + \
        HTML_BOTTOM

    fpdf = BytesIO()
    weasyprint.HTML(string=df_html).write_pdf(fpdf)

    output = PyPDF2.PdfFileWriter()
    input_pdf = PyPDF2.PdfFileReader(fpdf)

    for i in range(0, input_pdf.getNumPages()):
        output.addPage(input_pdf.getPage(i))

    output_pdf_fn = 'test.pdf'
    with open(output_pdf_fn, 'wb') as fout:
        if access_pwd is not None:
            output.encrypt(access_pwd, use_128bit=True)
        output.write(fout)

if __name__ == '__main__':
    main('Thomas Vincent', None, 'role_pwd')






















def html_basic(df: pd.DataFrame) -> str:
    # Using df.style.render outputs an id in every cell,
    # whilst using df.to_html doesn't.
    return df.style.render()


def write_pdf_autofit(df: pd.DataFrame,
                      preamble: str,
                      fn_df_to_html: Callable[[pd.DataFrame], str]=html_basic
                      ) -> bytes:
    template = f"""<html><body>{preamble}{{table}}</body></html>"""

    # Render on a very long page so that there's no pagination.
    # Width doesn't matter, because overflow is allowed on width.
    mycss = wp.CSS(string=(
        "@page longpage {\n"
        "    size: 210mm 10000mm;\n"
        "}"
        "body {\n"
        "   page: longpage;\n"
        "}\n"
    ))

    # Create a copy of the dataframe with a dummy final column,
    # so that we can get the position of the left side of the
    # dummy column which is the right side of the final real column.
    # Then do a test render to find the positions of stuff.
    df_tmp = df.copy()
    df_tmp['x'] = np.nan
    test_html = template.format(table=fn_df_to_html(df_tmp))
    test_render = wp.HTML(string=test_html).render(stylesheets=[mycss])
    test_page1: wp.Page = test_render.pages[0]

    # I'm not sure why only need to subtract one margin,
    # but seems to work.
    printable_width = test_page1.width - test_page1._page_box.margin_left
    printable_height = 11.7 * 96 - test_page1._page_box.margin_top

    # All the cells in the html rendered DataFrame
    # have an id so are anchors, so just find the
    # max x and y from all the anchors.
    max_x, max_y = map(max, *test_page1.anchors.values())
    zoom_pct = 1
    if max_x > printable_width or max_y > printable_height:
        zoom_pct = min([printable_width / max_x,
                        printable_height / max_y])

    # Increase the page size to fit the table, then
    # we will zoom out the write_pdf to fit standard page size.
    # A4 = 210mm x 297mm
    mycss = wp.CSS(string=(
        "@page scaled {\n"
        f"    size: {210 / zoom_pct}mm {297 / zoom_pct}mm;\n"
        "}"
        "body {\n"
        "   page: scaled;\n"
        "}\n"
    ))

    html = template.format(table=fn_df_to_html(df))
    pdf_bytes = wp.HTML(string=html).write_pdf(zoom=zoom_pct,
                                               stylesheets=[mycss])
    return pdf_bytes


if __name__ == "__main__":
    import numpy as np
    DF = pd.DataFrame(np.random.randint(0, 100, size=(100, 4)), columns=list('ABCD'))
    with open(r'c:\temp\x.pdf', 'wb') as f:
        f.write(write_pdf_autofit(DF, ""))
