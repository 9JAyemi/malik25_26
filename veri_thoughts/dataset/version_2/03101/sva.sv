module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [7:0] out1,
    input logic [7:0] out2
);

    // out1 follows the selected branch from the low byte of the adder result.
    check_out1_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        (
            ((({8'b0, a} + {8'b0, b})[7:0] > 8'h55) && (out1 == ({8'b0, a} + {8'b0, b})[7:0])) ||
            ((({8'b0, a} + {8'b0, b})[7:0] < 8'h55) && (out1 == c)) ||
            ((({8'b0, a} + {8'b0, b})[7:0] == 8'h55) && (out1 == a))
        )
    );

    // out2 follows the selected branch from the low byte of the adder result.
    check_out2_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        (
            ((({8'b0, a} + {8'b0, b})[7:0] > 8'h55) && (out2 == 8'b0)) ||
            ((({8'b0, a} + {8'b0, b})[7:0] < 8'h55) && (out2 == d)) ||
            ((({8'b0, a} + {8'b0, b})[7:0] == 8'h55) && (out2 == b))
        )
    );

    // Greater-than comparison drives sum low byte to out1 and zero to out2.
    check_gt_branch_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (({8'b0, a} + {8'b0, b})[7:0] > 8'h55) |-> (
            (out1 == ({8'b0, a} + {8'b0, b})[7:0]) &&
            (out2 == 8'b0)
        )
    );

    // Less-than comparison drives c to out1 and d to out2.
    check_lt_branch_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (({8'b0, a} + {8'b0, b})[7:0] < 8'h55) |-> (
            (out1 == c) &&
            (out2 == d)
        )
    );

    // Equality comparison drives a to out1 and b to out2.
    check_eq_branch_outputs: assert property (
        @(posedge clk) disable iff (reset)
        (({8'b0, a} + {8'b0, b})[7:0] == 8'h55) |-> (
            (out1 == a) &&
            (out2 == b)
        )
    );

endmodule