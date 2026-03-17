module f1_test_sva (
    input logic clk,
    input logic in,
    input logic out
);
    // out directly mirrors in.
    check_f1_out_passthrough: assert property (
        @(posedge clk) out == in
    );
endmodule

module f2_test_sva (
    input logic clk,
    input logic in,
    input logic out
);
    // out is the bitwise inversion of in.
    check_f2_out_inverts_in: assert property (
        @(posedge clk) out == ~in
    );
endmodule

module f3_test_sva (
    input logic clk,
    input logic [1:0] in,
    input logic select,
    input logic out
);
    // out matches the bit selected by select.
    check_f3_selected_bit: assert property (
        @(posedge clk) out == in[select]
    );
endmodule

module f4_test_sva (
    input logic clk,
    input logic [127:0] in,
    input logic [6:0] select,
    input logic out
);
    // out matches the selected bit of the 128-bit input bus.
    check_f4_selected_bit: assert property (
        @(posedge clk) out == in[select]
    );
endmodule

module f5_test_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [2:0] select,
    input logic out
);
    // out matches the selected bit of the 8-bit input bus.
    check_f5_selected_bit: assert property (
        @(posedge clk) out == in[select]
    );
endmodule