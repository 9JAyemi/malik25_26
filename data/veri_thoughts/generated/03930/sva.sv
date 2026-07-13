module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // Top output must equal the truncated sum masked by the selected mux input.
    check_out_matches_selected_sum: assert property (
        @(posedge clk)
        out == ((({1'b0, A} + {1'b0, B})[3:0]) &
                ((sel == 2'b00) ? in0 :
                 ((sel == 2'b01) ? in1 :
                  ((sel == 2'b10) ? in2 : in3))))
    );

    // sel=00 must route in0 through the final AND with the adder result.
    check_sel0_uses_in0: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> (out == ((({1'b0, A} + {1'b0, B})[3:0]) & in0))
    );

    // sel=01 must route in1 through the final AND with the adder result.
    check_sel1_uses_in1: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> (out == ((({1'b0, A} + {1'b0, B})[3:0]) & in1))
    );

    // sel=10 must route in2 through the final AND with the adder result.
    check_sel2_uses_in2: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> (out == ((({1'b0, A} + {1'b0, B})[3:0]) & in2))
    );

    // sel=11 must route in3 through the final AND with the adder result.
    check_sel3_uses_in3: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> (out == ((({1'b0, A} + {1'b0, B})[3:0]) & in3))
    );

    // A zero selected mux input must force the output low.
    check_zero_selected_input_forces_zero_out: assert property (
        @(posedge clk)
        (((sel == 2'b00) ? in0 :
          ((sel == 2'b01) ? in1 :
           ((sel == 2'b10) ? in2 : in3))) == 4'b0000) |-> (out == 4'b0000)
    );

    // A zero low-order adder sum must force the output low.
    check_zero_sum_forces_zero_out: assert property (
        @(posedge clk)
        ((({1'b0, A} + {1'b0, B})[3:0]) == 4'b0000) |-> (out == 4'b0000)
    );

    // An all-ones selected mux input must pass the low-order adder sum unchanged.
    check_all_ones_selected_input_passes_sum: assert property (
        @(posedge clk)
        (((sel == 2'b00) ? in0 :
          ((sel == 2'b01) ? in1 :
           ((sel == 2'b10) ? in2 : in3))) == 4'b1111)
        |-> (out == (({1'b0, A} + {1'b0, B})[3:0]))
    );

    // Output bits can only be high where the selected mux input is high.
    check_out_is_masked_by_selected_input: assert property (
        @(posedge clk)
        (out & ~((sel == 2'b00) ? in0 :
                 ((sel == 2'b01) ? in1 :
                  ((sel == 2'b10) ? in2 : in3)))) == 4'b0000
    );

    // Output bits can only be high where the low-order adder sum is high.
    check_out_is_masked_by_sum: assert property (
        @(posedge clk)
        (out & ~((({1'b0, A} + {1'b0, B})[3:0]))) == 4'b0000
    );

endmodule