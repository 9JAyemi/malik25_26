module BrzVariable_17_1_s0__sva (
    input  logic        write_0r,
    input  logic        write_0a,
    input  logic [16:0] write_0d,
    input  logic        read_0r,
    input  logic        read_0a,
    input  logic [16:0] read_0d
);
    // On a write_0r rising edge, write_0a must be low (since write_0a = ~write_0r).
    check_write_ack_low_on_write_edge: assert property (
        @(posedge write_0r) write_0a == 1'b0
    );

    // On a write_0r rising edge, write_0a equals bitwise NOT of write_0r.
    check_write_ack_inverse_on_write_edge: assert property (
        @(posedge write_0r) write_0a == ~write_0r
    );

    // On a write_0r rising edge, write_0r and write_0a are never both HIGH.
    check_write_req_ack_mutex: assert property (
        @(posedge write_0r) !(write_0r && write_0a)
    );

    // On a write_0r rising edge, exactly one of {write_0r, write_0a} is HIGH.
    check_write_req_ack_onehot: assert property (
        @(posedge write_0r) $onehot({write_0r, write_0a})
    );

    // read_0a is a combinational pass-through of read_0r.
    check_read_accept_passthrough: assert property (
        @(posedge write_0r) read_0a == read_0r
    );

    // read_0d remains stable across write_0r rising edges (no write occurs at the edge).
    check_read_data_stable_on_write_edge: assert property (
        @(posedge write_0r) $stable(read_0d)
    );

    // write_0a remains stable across consecutive write_0r rising edges (always 0 at the edge).
    check_write_ack_stable_on_write_edges: assert property (
        @(posedge write_0r) $stable(write_0a)
    );
endmodule