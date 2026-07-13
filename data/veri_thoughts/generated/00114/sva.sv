module data_parser_sva(
    input logic clk,
    input logic [3:0] data_in,
    input logic [1:0] data_out_1,
    input logic [1:0] data_out_2,
    input logic parity
);

    // data_out_1 mirrors the low two bits of data_in.
    check_data_out_1_slice: assert property (
        @(posedge clk) data_out_1 == data_in[1:0]
    );

    // data_out_2 mirrors the high two bits of data_in.
    check_data_out_2_slice: assert property (
        @(posedge clk) data_out_2 == data_in[3:2]
    );

    // parity is the reduction XOR of data_in.
    check_parity_from_input: assert property (
        @(posedge clk) parity == (^data_in)
    );

    // The two output fields reconstruct the full input bus.
    check_outputs_reconstruct_input: assert property (
        @(posedge clk) {data_out_2, data_out_1} == data_in
    );

    // parity matches the XOR of the split output fields.
    check_parity_from_outputs: assert property (
        @(posedge clk) parity == (^({data_out_2, data_out_1}))
    );

endmodule