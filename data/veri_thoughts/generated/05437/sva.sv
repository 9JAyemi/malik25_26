module ALU_sva (
    input logic clk,
    input logic [3:0] control,
    input logic signed [31:0] data_input1,
    input logic signed [31:0] data_input2,
    input logic signed [31:0] data_output,
    input logic zero
);

    // Add control computes the sum and clears zero.
    check_add_operation: assert property (
        @(posedge clk)
        (control == 4'b0010) |=> ((data_output == ($past(data_input1) + $past(data_input2))) &&
                                  (zero == 1'b0))
    );

    // Subtract control computes the difference and sets zero only for a zero result.
    check_sub_operation: assert property (
        @(posedge clk)
        (control == 4'b0110) |=> ((data_output == ($past(data_input1) - $past(data_input2))) &&
                                  (zero == (($past(data_input1) - $past(data_input2)) == 32'sd0)))
    );

    // AND control computes the bitwise AND and clears zero.
    check_and_operation: assert property (
        @(posedge clk)
        (control == 4'b0000) |=> ((data_output == ($past(data_input1) & $past(data_input2))) &&
                                  (zero == 1'b0))
    );

    // OR control computes the bitwise OR and clears zero.
    check_or_operation: assert property (
        @(posedge clk)
        (control == 4'b0001) |=> ((data_output == ($past(data_input1) | $past(data_input2))) &&
                                  (zero == 1'b0))
    );

    // SLT control outputs 1 when input1 is greater than input2, else 0, and clears zero.
    check_slt_operation: assert property (
        @(posedge clk)
        (control == 4'b0111) |=> ((data_output == (($past(data_input2) < $past(data_input1)) ? 32'sd1 : 32'sd0)) &&
                                  (zero == 1'b0))
    );

    // NOR control computes the bitwise NOR and clears zero.
    check_nor_operation: assert property (
        @(posedge clk)
        (control == 4'b1100) |=> ((data_output == ~($past(data_input1) | $past(data_input2))) &&
                                  (zero == 1'b0))
    );

    // Any unsupported control drives a zero output and clears zero.
    check_default_operation: assert property (
        @(posedge clk)
        ((control != 4'b0010) &&
         (control != 4'b0110) &&
         (control != 4'b0000) &&
         (control != 4'b0001) &&
         (control != 4'b0111) &&
         (control != 4'b1100)) |=> ((data_output == 32'sd0) &&
                                    (zero == 1'b0))
    );

endmodule