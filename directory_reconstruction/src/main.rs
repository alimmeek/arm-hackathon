use core::panic;
use fxhash::FxHashSet;
use std::io;

const MAX_PATH_LEN: usize = 300;

fn main() {
    // output counters
    let mut file_total: u32 = 0;
    let mut current_depth: u32 = 0;
    let mut depth_acc: u32 = 0;
    let mut current_path: [u8; MAX_PATH_LEN] = [0; 300];
    current_path[0] = b'/';
    let mut current_path_pos: usize = 0;
    let mut max_depth: u32 = 0;
    let mut max_path: [u8; MAX_PATH_LEN] = [0; 300];
    let mut max_path_len: usize = 0;
    let mut visited = FxHashSet::default();
    let mut should_chck = false;
    // allocate buffer
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
                                        current_path_pos = 1;
                                        current_path[0] = b'/';
                                    }
                                    // moved to parent
                                    '.' => {
                                        current_depth -= 1;
                                        while current_path[current_path_pos] != b'/' {
                                            current_path_pos -= 1
                                        }
                                        current_path_pos += 1;
                                    }
                                    // moved to child
                                    _ => {
                                        current_depth += 1;
                                        max_depth = std::cmp::max(current_depth, max_depth);
                                        let len = buffer.len();
                                        let name_len = len - 6;
                                        current_path[current_path_pos..current_path_pos + name_len]
                                            .copy_from_slice(&buffer.as_bytes()[5..len - 1]);
                                        current_path_pos += name_len;
                                        current_path[current_path_pos] = b'/';
                                        current_path_pos += 1;
                                    }
                                }
                            }
                            // ls commanmd
                            'l' => {
                                current_path[current_path_pos + 1..].fill(0);
                                should_chck = visited.insert(current_path);
                            }
                            _ => panic!("Unknown Command"),
                        }
                    }
                    // ls output directory
                    'd' => {}
                    // ls output file
                    _ => {
                        if should_chck {
                            file_total += 1;
                            depth_acc += current_depth;
                            if current_depth == max_depth {
                                let start_i = buffer.find(' ').unwrap() + 1;
                                let name_size = buffer.len() - 1 - start_i;
                                max_path[..current_path_pos]
                                    .copy_from_slice(&current_path[..current_path_pos]);
                                max_path[current_path_pos..current_path_pos + name_size]
                                    .copy_from_slice(&buffer.as_bytes()[start_i..buffer.len() - 1]);
                                max_path_len = current_path_pos + name_size;
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
        std::str::from_utf8(&max_path[..max_path_len]).unwrap(),
        depth_acc as f32 / file_total as f32
    );
}
