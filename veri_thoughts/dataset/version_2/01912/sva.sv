module bit_counter_sva (
    input logic [3:0] in,
    input logic [1:0] out
);
    // When in == 0000, out must be 00.
    check_map_0000: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0000) |-> (out == 2'b00)
    );
    // When in == 0001, out must be 01.
    check_map_0001: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0001) |-> (out == 2'b01)
    );
    // When in == 0010, out must be 01.
    check_map_0010: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0010) |-> (out == 2'b01)
    );
    // When in == 0011, out must be 10.
    check_map_0011: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0011) |-> (out == 2'b10)
    );
    // When in == 0100, out must be 01.
    check_map_0100: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0100) |-> (out == 2'b01)
    );
    // When in == 0101, out must be 10.
    check_map_0101: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0101) |-> (out == 2'b10)
    );
    // When in == 0110, out must be 10.
    check_map_0110: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0110) |-> (out == 2'b10)
    );
    // When in == 0111, out must be 11.
    check_map_0111: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b0111) |-> (out == 2'b11)
    );
    // When in == 1000, out must be 01.
    check_map_1000: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1000) |-> (out == 2'b01)
    );
    // When in == 1001, out must be 10.
    check_map_1001: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1001) |-> (out == 2'b10)
    );
    // When in == 1010, out must be 10.
    check_map_1010: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1010) |-> (out == 2'b10)
    );
    // When in == 1011, out must be 11.
    check_map_1011: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1011) |-> (out == 2'b11)
    );
    // When in == 1100, out must be 10.
    check_map_1100: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1100) |-> (out == 2'b10)
    );
    // When in == 1101, out must be 11.
    check_map_1101: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1101) |-> (out == 2'b11)
    );
    // When in == 1110, out must be 11.
    check_map_1110: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1110) |-> (out == 2'b11)
    );
    // When in == 1111, out must be 11.
    check_map_1111: assert property (
        @(posedge in[0] or posedge in[1] or posedge in[2] or posedge in[3]) (in == 4'b1111) |-> (out == 2'b11)
    );
endmodule