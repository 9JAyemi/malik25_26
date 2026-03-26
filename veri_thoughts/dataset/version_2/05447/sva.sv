module c_nand_nto1_sva #(
    parameter int num_ports = 2,
    parameter int width = 1
) (
    input logic clk,
    input logic [0:width*num_ports-1] data_in,
    input logic [0:width-1] data_out
);

    function automatic logic aligned_inputs_and(
        input logic [0:width*num_ports-1] din,
        input integer bit_idx
    );
        integer k;
        logic and_val;
        begin
            and_val = 1'b1;
            for (k = 0; k < num_ports; k = k + 1)
                and_val = and_val & din[k*width + bit_idx];
            aligned_inputs_and = and_val;
        end
    endfunction

    genvar i;
    generate
        for (i = 0; i < width; i = i + 1) begin : bit_positions
            // Output bit equals the NAND of the aligned input bits.
            check_nand_function: assert property (
                @(posedge clk) data_out[i] === (~aligned_inputs_and(data_in, i))
            );

            // All aligned inputs high drive the output low.
            check_all_ones_drive_zero: assert property (
                @(posedge clk) (aligned_inputs_and(data_in, i) === 1'b1) |-> (data_out[i] === 1'b0)
            );

            // Any aligned zero drives the output high.
            check_any_zero_drive_one: assert property (
                @(posedge clk) (aligned_inputs_and(data_in, i) === 1'b0) |-> (data_out[i] === 1'b1)
            );

            // A low output only occurs when all aligned inputs are high.
            check_low_output_requires_all_ones: assert property (
                @(posedge clk) (data_out[i] === 1'b0) |-> (aligned_inputs_and(data_in, i) === 1'b1)
            );
        end
    endgenerate

endmodule