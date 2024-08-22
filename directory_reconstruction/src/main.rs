use core::panic;
use fxhash::FxHashSet;
use std::io;

const MAX_PATH_LEN: usize = 300;

struct StackString {
    data: [u8; MAX_PATH_LEN],
    pos: usize,
}

impl StackString {
    fn new() -> Self {
        Self {
            pos: 0,
            data: [0; MAX_PATH_LEN],
        }
    }

    fn append(&mut self, data: &[u8], size: usize) {
        self.data[self.pos..self.pos + size].copy_from_slice(data);
        self.pos += size;
    }
}

fn main() {
    // file total output
    let mut file_total: u32 = 0;

    // average depth output
    let mut current_depth: u32 = 0;
    let mut depth_acc: u32 = 0;

    // deepest nested file output
    let mut current_path = StackString::new();
    current_path.data[0] = b'/';
    let mut max_depth: u32 = 0;
    let mut max_path = StackString::new();
    let mut visited = FxHashSet::default();
    let mut should_chck = false;

    // allocate iput buffer
    let mut buffer = String::new();
    buffer.reserve(MAX_PATH_LEN);
    // read in input
    loop {
        match io::stdin().read_line(&mut buffer) {
            Ok(n) => {
                // no more lines
                if n == 0 {
                    break;
                };
                let mut chars = buffer.chars();
                match chars.nth(0).unwrap() {
                    // command
                    '$' => {
                        // check command type
                        match chars.nth(1).unwrap() {
                            // cd command
                            'c' => {
                                match chars.nth(2).unwrap() {
                                    // moved to root
                                    '/' => {
                                        current_depth = 0;
                                        current_path.pos = 1;
                                        current_path.data[0] = b'/';
                                    }
                                    // moved to parent
                                    '.' => {
                                        current_depth -= 1;
                                        while current_path.data[current_path.pos] != b'/' {
                                            current_path.pos -= 1
                                        }
                                        current_path.pos += 1;
                                    }
                                    // moved to child
                                    _ => {
                                        // increase depth counters
                                        current_depth += 1;
                                        max_depth = std::cmp::max(current_depth, max_depth);

                                        // append directory to current path
                                        let len = buffer.len();
                                        let name_len = len - 6;
                                        current_path
                                            .append(&buffer.as_bytes()[5..len - 1], name_len);
                                        // append separator
                                        current_path.data[current_path.pos] = b'/';
                                        current_path.pos += 1;
                                    }
                                }
                            }
                            // ls commanmd
                            'l' => {
                                // check if it is a unique listing
                                current_path.data[current_path.pos + 1..].fill(0);
                                should_chck = visited.insert(current_path.data);
                            }
                            // a command different than ls or cd was issued
                            _ => panic!("Unknown Command"),
                        }
                    }
                    // ls output directory
                    'd' => {}
                    // ls output file
                    _ => {
                        // skip non unique listings
                        if should_chck {
                            // increment file counters
                            file_total += 1;
                            depth_acc += current_depth;
                            // chech if this is most nested file so far
                            if current_depth == max_depth {
                                // find name of file
                                let start_i = buffer.find(' ').unwrap() + 1;
                                let name_size = buffer.len() - 1 - start_i;
                                // copy current ffiel path
                                max_path.pos = 0;
                                max_path.append(
                                    &current_path.data[..current_path.pos],
                                    current_path.pos,
                                );
                                max_path.append(
                                    &buffer.as_bytes()[start_i..buffer.len() - 1],
                                    name_size,
                                );
                            }
                        }
                    }
                }

                // discard previous line
                buffer.clear();
            }
            Err(_) => break,
        }
    }
    // print putput
    println!(
        "{},{},{}",
        file_total,
        std::str::from_utf8(&max_path.data[..max_path.pos]).unwrap(),
        depth_acc as f32 / file_total as f32
    );
}
