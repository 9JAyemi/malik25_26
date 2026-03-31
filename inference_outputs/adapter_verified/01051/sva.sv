module ssio_sdr_in_sva (
    input logic             input_clk,
    input logic [WIDTH-1:0] input_d,
    input logic             output_clk,
    input logic [WIDTH-1:0] output_q
);

// output_clk is a direct copy of input_clk.
    check_output_clk_passthrough: assert property (
        @(posedge input_clk) output_clk == input_clk
    );

// output_q captures input_d on the next rising edge of input_clk.
    check_output_q_capture: assert property (
        @(posedge input_clk) 1'b1 |=> (output_q == $past(input_d))
    );

// output_q holds its value when input_d does not change.
    check_output_q_stable_when_input_d_stable: assert property (
        @(posedge input_clk) 1'b1 |=> ((input_d == $past(input_d)) |-> (output_q == $past(output_q)))
    );

// output_q changes when input_d changes.
    check_output_q_changes_when_input_d_changes: assert property (
        @(posedge input_clk) 1'b1 |=> ((input_d != $past(input_d)) |-> (output_q != $past(output_q)))
    );

endmodule
