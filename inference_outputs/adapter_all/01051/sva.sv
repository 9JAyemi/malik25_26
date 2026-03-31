module ssio_sdr_in_sva #(
    parameter TARGET = "GENERIC",
    parameter CLOCK_INPUT_STYLE = "BUFIO2",
    parameter WIDTH = 1
) (
    input  logic             input_clk,
    input  logic [WIDTH-1:0] input_d,
    input  logic             output_clk,
    input  logic [WIDTH-1:0] output_q
);

    // No RTL clock or reset; sample combinational behavior on input_clk.

    // output_clk is a direct copy of input_clk for Xilinx styles.
    check_output_clk_matches_input_clk_xilinx: assert property (
        @(posedge input_clk) (TARGET == "XILINX") |-> (output_clk == input_clk)
    );

    // output_clk is a direct copy of input_clk for non-Xilinx targets.
    check_output_clk_matches_input_clk_generic: assert property (
        @(posedge input_clk) (TARGET != "XILINX") |-> (output_clk == input_clk)
    );

    // output_q captures input_d on each rising edge of output_clk.
    check_output_q_captures_input_d: assert property (
        @(posedge output_clk) output_q == $past(input_d)
    );

    // output_q holds its value when output_clk is low.
    check_output_q_stable_when_output_clk_low: assert property (
        @(negedge output_clk) $stable(output_q)
    );

    // output_q holds its value when output_clk is high.
    check_output_q_stable_when_output_clk_high: assert property (
        @(posedge output_clk) $stable(output_q)
    );

    // output_q changes only after an output_clk rising edge.
    check_output_q_changes_only_on_output_clk: assert property (
        @(posedge input_clk) $changed(output_q) |-> $rose(output_clk)
    );

    // output_q reflects the input_d value from the previous output_clk edge.
    check_output_q_matches_previous_input_d: assert property (
        @(posedge output_clk) output_q == $past(input_d)
    );

endmodule