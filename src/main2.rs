use prsqlite::btree::cell_pointer_offset;
use prsqlite::btree::parse_btree_leaf_table_cell;
use prsqlite::btree::BtreePageHeader;
use prsqlite::test_utils::create_pager;
use prsqlite::test_utils::load_btree_context;

const DB_PATH: &str = "tmp/sqlite.db";

fn main() {
    let conn = rusqlite::Connection::open(DB_PATH).unwrap();
    conn.execute("CREATE TABLE example(col);", []).unwrap();

    let ctx = load_btree_context(&std::fs::File::open(DB_PATH).unwrap()).unwrap();

    let v = n_cells();

    let mut n_pages = v.len();
    println!("{:?}", v);
    let mut prev = v;

    let mut head = 0;
    let mut tail = 0;
    let mut cell_size = 0;
    for i in 0..100000 {
        let v = i32::MAX - i;
        // let v = i;
        conn.execute(
            &format!("INSERT INTO example(rowid, col) VALUES ({}, 127);", v),
            [],
        )
        .unwrap();
        let v = n_cells();
        if v.len() != n_pages {
            n_pages = v.len();
            println!("{:?} -> {:?}", prev, v);
            println!("cell size: {cell_size}");
            println!("{}, {}, {}", tail as usize - head, head, tail);
        }
        if n_pages > 3 {
            let pager = create_pager(std::fs::File::open(DB_PATH).unwrap()).unwrap();
            let page = pager.get_page(3).unwrap();
            let buffer = page.buffer();
            let header = BtreePageHeader::from_page(&page, &buffer);

            head = cell_pointer_offset(&page, header.n_cells(), header.header_size());
            tail = header.cell_content_area_offset();
            let (_, payload) = parse_btree_leaf_table_cell(&ctx, &page, &buffer, 0).unwrap();
            cell_size = payload.payload_size;
            // println!("{}, {}, {}", tail as usize - head, head, tail);
        }
        prev = v;
    }
}

fn n_cells() -> Vec<u16> {
    let pager = create_pager(std::fs::File::open(DB_PATH).unwrap()).unwrap();
    let mut result = Vec::new();
    for i in 1..=pager.num_pages() {
        let page = pager.get_page(i).unwrap();
        let buffer = page.buffer();
        let header = BtreePageHeader::from_page(&page, &buffer);
        let n_cells = header.n_cells();
        result.push(n_cells);
    }
    result
}
