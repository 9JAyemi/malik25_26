module bmod_sva (
    input logic clk,
    input logic [2:0] in_row,
    input logic [4:0] out_code
);

    localparam [4:0] D_0 = 5'b10011;
    localparam [4:0] D_1 = 5'b01011;
    localparam [4:0] D_2 = 5'b00100;
    localparam [4:0] D_3 = 5'b11010;
    localparam [4:0] D_4 = 5'b11001;

    // 000 maps to d_0.
    check_map_row_000: assert property (
        @(posedge clk) (in_row == 3'b000) |-> (out_code == D_0)
    );

    // 001 maps to d_1.
    check_map_row_001: assert property (
        @(posedge clk) (in_row == 3'b001) |-> (out_code == D_1)
    );

    // 010 maps to d_2.
    check_map_row_010: assert property (
        @(posedge clk) (in_row == 3'b010) |-> (out_code == D_2)
    );

    // 011 maps to d_3.
    check_map_row_011: assert property (
        @(posedge clk) (in_row == 3'b011) |-> (out_code == D_3)
    );

    // 100 maps to d_4.
    check_map_row_100: assert property (
        @(posedge clk) (in_row == 3'b100) |-> (out_code == D_4)
    );

    // 101 selects the default zero code.
    check_map_row_101: assert property (
        @(posedge clk) (in_row == 3'b101) |-> (out_code == 5'b00000)
    );

    // 110 selects the default zero code.
    check_map_row_110: assert property (
        @(posedge clk) (in_row == 3'b110) |-> (out_code == 5'b00000)
    );

    // 111 selects the default zero code.
    check_map_row_111: assert property (
        @(posedge clk) (in_row == 3'b111) |-> (out_code == 5'b00000)
    );

endmodule