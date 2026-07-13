module next_highest_sva (
    input logic [3:0] in,
    input logic clk,
    input logic [3:0] out
);

    // Clock: clk; no reset in RTL; logic is combinational pre-processing plus a registered output.
    function automatic logic [3:0] rtl_result(input logic [3:0] val);
        logic [3:0] stage1_calc;
        begin
            stage1_calc = val + 4'd1;
            if (stage1_calc == 4'hf)
                rtl_result = 4'h0;
            else
                rtl_result = stage1_calc;
        end
    endfunction

    // Output updates on the next clock to the value computed from the sampled input.
    check_registered_transfer: assert property (
        @(posedge clk) 1'b1 |=> (out == rtl_result($past(in)))
    );

    // Inputs 0 through 13 increment by one on the next clock.
    check_low_range_increment: assert property (
        @(posedge clk) (in <= 4'd13) |=> (out == ($past(in) + 4'd1))
    );

    // Input 13 reaches the upper non-zero boundary value 14 on the next clock.
    check_input_13_to_14: assert property (
        @(posedge clk) (in == 4'd13) |=> (out == 4'd14)
    );

    // Input 14 produces zero on the next clock because stage1 hits 4'hf.
    check_input_14_to_zero: assert property (
        @(posedge clk) (in == 4'd14) |=> (out == 4'd0)
    );

    // Input 15 also produces zero on the next clock because the 4-bit increment wraps.
    check_input_15_to_zero: assert property (
        @(posedge clk) (in == 4'd15) |=> (out == 4'd0)
    );

    // The registered output can never be 4'hf after a clocked update.
    check_output_never_fifteen: assert property (
        @(posedge clk) 1'b1 |=> (out != 4'hf)
    );

    // Zero output occurs only when the previously sampled input was 14 or 15.
    check_zero_output_source: assert property (
        @(posedge clk) 1'b1 |=> ((out == 4'd0) == (($past(in) == 4'd14) || ($past(in) == 4'd15)))
    );

endmodule