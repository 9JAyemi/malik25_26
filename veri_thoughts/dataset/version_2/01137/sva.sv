module shift_mux_adder_sva (
    input logic clk,
    input logic [7:0] data_in_0,
    input logic [7:0] data_in_1,
    input logic [7:0] data_in_2,
    input logic [7:0] data_in_3,
    input logic [3:0] B,
    input logic sel1,
    input logic sel2,
    input logic [7:0] out
);
    // When B>3, out is forced to zero.
    check_B_gt3_zero: assert property (
        @(posedge clk) (B > 4'd3) |-> (out == 8'b0)
    );

    // For B<=3, out equals selected input left-shifted by B.
    check_B_le3_selected_shift: assert property (
        @(posedge clk) (B <= 4'd3) |-> (out == (((sel2 == 1'b0) ? ((sel1 == 1'b0) ? data_in_0 : data_in_1)
                                                                 : ((sel1 == 1'b0) ? data_in_2 : data_in_3)) << B))
    );

    // For B<=3 and sel=00, out equals data_in_0 << B.
    check_sel00_shift: assert property (
        @(posedge clk) ((B <= 4'd3) && (sel2 == 1'b0) && (sel1 == 1'b0)) |-> (out == (data_in_0 << B))
    );

    // For B<=3 and sel=01, out equals data_in_1 << B.
    check_sel01_shift: assert property (
        @(posedge clk) ((B <= 4'd3) && (sel2 == 1'b0) && (sel1 == 1'b1)) |-> (out == (data_in_1 << B))
    );

    // For B<=3 and sel=10, out equals data_in_2 << B.
    check_sel10_shift: assert property (
        @(posedge clk) ((B <= 4'd3) && (sel2 == 1'b1) && (sel1 == 1'b0)) |-> (out == (data_in_2 << B))
    );

    // For B<=3 and sel=11, out equals data_in_3 << B.
    check_sel11_shift: assert property (
        @(posedge clk) ((B <= 4'd3) && (sel2 == 1'b1) && (sel1 == 1'b1)) |-> (out == (data_in_3 << B))
    );

    // For B==0, out passes through the selected input.
    check_B0_passthrough: assert property (
        @(posedge clk) (B == 4'd0) |-> (out == ((sel2 == 1'b0) ? ((sel1 == 1'b0) ? data_in_0 : data_in_1)
                                                              : ((sel1 == 1'b0) ? data_in_2 : data_in_3)))
    );

    // For B==1, LSB of out is zero due to left shift.
    check_B1_zero_fill: assert property (
        @(posedge clk) (B == 4'd1) |-> (out[0] == 1'b0)
    );

    // For B==2, two LSBs of out are zero due to left shift.
    check_B2_zero_fill: assert property (
        @(posedge clk) (B == 4'd2) |-> (out[1:0] == 2'b00)
    );

    // For B==3, three LSBs of out are zero due to left shift.
    check_B3_zero_fill: assert property (
        @(posedge clk) (B == 4'd3) |-> (out[2:0] == 3'b000)
    );
endmodule