module sdio_function_template_assertions (
    input logic       clk,
    input logic       rst,
    input logic [7:0] o_reg_example,
    input logic [7:0] i_reg_example,
    input logic [7:0] temp_reg
);

    // Output reflects temp_reg sampled on the previous clk edge.
    check_output_captures_previous_temp_reg: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> (o_reg_example == $past(temp_reg))
    );

    // temp_reg reflects i_reg_example sampled on the previous rst edge.
    check_temp_reg_captures_previous_input_on_rst: assert property (
        @(posedge rst) disable iff (1'b0)
        1'b1 |=> (temp_reg == $past(i_reg_example))
    );

    // If temp_reg is unchanged across clk samples, output matches current temp_reg.
    check_output_matches_current_temp_when_temp_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ((temp_reg == $past(temp_reg)) |-> (o_reg_example == temp_reg))
    );

    // If temp_reg changes between clk samples, output still lags current temp_reg.
    check_output_lags_current_temp_when_temp_changes: assert property (
        @(posedge clk) disable iff (1'b0)
        1'b1 |=> ((temp_reg != $past(temp_reg)) |-> (o_reg_example != temp_reg))
    );

    // If input is unchanged across rst samples, temp_reg matches current input.
    check_temp_matches_current_input_when_input_stable: assert property (
        @(posedge rst) disable iff (1'b0)
        1'b1 |=> ((i_reg_example == $past(i_reg_example)) |-> (temp_reg == i_reg_example))
    );

    // If input changes between rst samples, temp_reg still lags current input.
    check_temp_lags_current_input_when_input_changes: assert property (
        @(posedge rst) disable iff (1'b0)
        1'b1 |=> ((i_reg_example != $past(i_reg_example)) |-> (temp_reg != i_reg_example))
    );

endmodule