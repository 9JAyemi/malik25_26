module next_higher_binary_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [3:0] out
);
    // When in==0000, out must be 0001.
    check_map_0000_to_0001: assert property (
        @(posedge CLK) (in == 4'b0000) |=> (out == 4'b0001)
    );
    // When in==0001, out must be 0010.
    check_map_0001_to_0010: assert property (
        @(posedge CLK) (in == 4'b0001) |=> (out == 4'b0010)
    );
    // When in==0010, out must be 0011.
    check_map_0010_to_0011: assert property (
        @(posedge CLK) (in == 4'b0010) |=> (out == 4'b0011)
    );
    // When in==0011, out must be 0100.
    check_map_0011_to_0100: assert property (
        @(posedge CLK) (in == 4'b0011) |=> (out == 4'b0100)
    );
    // When in==0100, out must be 0101.
    check_map_0100_to_0101: assert property (
        @(posedge CLK) (in == 4'b0100) |=> (out == 4'b0101)
    );
    // When in==0101, out must be 0110.
    check_map_0101_to_0110: assert property (
        @(posedge CLK) (in == 4'b0101) |=> (out == 4'b0110)
    );
    // When in==0110, out must be 0111.
    check_map_0110_to_0111: assert property (
        @(posedge CLK) (in == 4'b0110) |=> (out == 4'b0111)
    );
    // When in==0111, out must be 1000.
    check_map_0111_to_1000: assert property (
        @(posedge CLK) (in == 4'b0111) |=> (out == 4'b1000)
    );
    // When in==1000, out must be 1001.
    check_map_1000_to_1001: assert property (
        @(posedge CLK) (in == 4'b1000) |=> (out == 4'b1001)
    );
    // When in==1001, out must be 1010.
    check_map_1001_to_1010: assert property (
        @(posedge CLK) (in == 4'b1001) |=> (out == 4'b1010)
    );
    // When in==1010, out must be 1011.
    check_map_1010_to_1011: assert property (
        @(posedge CLK) (in == 4'b1010) |=> (out == 4'b1011)
    );
    // When in==1011, out must be 1100.
    check_map_1011_to_1100: assert property (
        @(posedge CLK) (in == 4'b1011) |=> (out == 4'b1100)
    );
    // When in==1100, out must be 1101.
    check_map_1100_to_1101: assert property (
        @(posedge CLK) (in == 4'b1100) |=> (out == 4'b1101)
    );
    // When in==1101, out must be 1110.
    check_map_1101_to_1110: assert property (
        @(posedge CLK) (in == 4'b1101) |=> (out == 4'b1110)
    );
    // When in==1110, out must be 1111.
    check_map_1110_to_1111: assert property (
        @(posedge CLK) (in == 4'b1110) |=> (out == 4'b1111)
    );
    // When in==1111, out must wrap to 0000.
    check_map_1111_to_0000: assert property (
        @(posedge CLK) (in == 4'b1111) |=> (out == 4'b0000)
    );
endmodule