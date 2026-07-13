module Multiplexer_AC__parameterized69_sva
  #(parameter WIDTH = 1)
(
    input logic clk,
    input logic ctrl,
    input logic [WIDTH-1:0] D0,
    input logic [WIDTH-1:0] D1,
    input logic [WIDTH-1:0] S
);

    // The output always matches the mux select function.
    check_mux_function: assert property (
        @(posedge clk) S == (ctrl ? D1 : D0)
    );

    // When ctrl is low, the output selects D0.
    check_select_d0: assert property (
        @(posedge clk) !ctrl |-> (S == D0)
    );

    // When ctrl is high, the output selects D1.
    check_select_d1: assert property (
        @(posedge clk) ctrl |-> (S == D1)
    );

    // A rising ctrl causes the output to reflect D1.
    check_ctrl_rise_selects_d1: assert property (
        @(posedge clk) $rose(ctrl) |-> (S == D1)
    );

    // A falling ctrl causes the output to reflect D0.
    check_ctrl_fall_selects_d0: assert property (
        @(posedge clk) $fell(ctrl) |-> (S == D0)
    );

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_bit_checks
            // Each output bit matches the selected input bit.
            check_bit_mux_function: assert property (
                @(posedge clk) S[i] == (ctrl ? D1[i] : D0[i])
            );
        end
    endgenerate

endmodule