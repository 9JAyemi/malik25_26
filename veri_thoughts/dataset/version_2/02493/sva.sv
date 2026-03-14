module control_module_sva (
    input logic clk,
    input logic [7:0] data_in,
    input logic [1:0] control_in,
    input logic [7:0] data_out
);
    // When control_in==00, data_out passes through data_in.
    check_passthrough_value: assert property (
        @(posedge clk) (control_in == 2'b00) |-> (data_out == data_in)
    );

    // When control_in==01, data_out is bitwise NOT of data_in.
    check_invert_value: assert property (
        @(posedge clk) (control_in == 2'b01) |-> (data_out == ~data_in)
    );

    // When control_in==01, XOR with input is all 1s.
    check_invert_xor_allones: assert property (
        @(posedge clk) (control_in == 2'b01) |-> ((data_out ^ data_in) == 8'hFF)
    );

    // When control_in==10, LSB after left shift is 0.
    check_leftshift_lsb_zero: assert property (
        @(posedge clk) (control_in == 2'b10) |-> (data_out[0] == 1'b0)
    );

    // When control_in==10, upper bits shift left by 1.
    check_leftshift_upper_bits: assert property (
        @(posedge clk) (control_in == 2'b10) |-> (data_out[7:1] == data_in[6:0])
    );

    // When control_in==11, MSB after right shift is 0.
    check_rightshift_msb_zero: assert property (
        @(posedge clk) (control_in == 2'b11) |-> (data_out[7] == 1'b0)
    );

    // When control_in==11, lower bits shift right by 1.
    check_rightshift_lower_bits: assert property (
        @(posedge clk) (control_in == 2'b11) |-> (data_out[6:0] == data_in[7:1])
    );

    // When control_in==00, XOR with input is all 0s.
    check_passthrough_xor_allzeros: assert property (
        @(posedge clk) (control_in == 2'b00) |-> ((data_out ^ data_in) == 8'h00)
    );

    // For any control, data_out matches the selected transform.
    check_function_selection: assert property (
        @(posedge clk)
            data_out == (control_in == 2'b00 ? data_in :
                         control_in == 2'b01 ? ~data_in :
                         control_in == 2'b10 ? {data_in[6:0], 1'b0} :
                                               {1'b0, data_in[7:1]})
    );

    // If inputs are stable across a cycle, output remains stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({control_in, data_in}) |-> $stable(data_out)
    );
endmodule