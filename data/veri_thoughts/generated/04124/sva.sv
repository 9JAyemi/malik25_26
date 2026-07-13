module mux_4to1_sva (
    input logic clk,
    input logic [7:0] in0,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    input logic [1:0] sel,
    input logic [7:0] out
);

    // When sel is 00, out must match in0.
    check_select_in0: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b00) |-> (out == in0)
    );

    // When sel is 01, out must match in1.
    check_select_in1: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b01) |-> (out == in1)
    );

    // When sel is 10, out must match in2.
    check_select_in2: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b10) |-> (out == in2)
    );

    // When sel is 11, out must match in3.
    check_select_in3: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b11) |-> (out == in3)
    );

    // If sel and the selected input stay stable, out must stay stable.
    check_selected_input_stability: assert property (
        @(posedge clk) disable iff (1'b0)
        ($stable(sel) &&
         (((sel == 2'b00) && $stable(in0)) ||
          ((sel == 2'b01) && $stable(in1)) ||
          ((sel == 2'b10) && $stable(in2)) ||
          ((sel == 2'b11) && $stable(in3)))) |-> $stable(out)
    );

endmodule