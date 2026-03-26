module wireless_communication_sva #(
    parameter n = 8,
    parameter m = 3
)(
    input logic clk,
    input logic [n-2:0] in,
    input logic [m-3:0] out_data,
    input logic ack,
    input logic err
);

    typedef logic [m-3:0] out_data_t;

    wire protocol_select = in[n-2];
    wire [n-3:0] data_in = in[n-3:0];

    // Protocol 0 echoes the sampled input data.
    check_protocol0_out_data: assert property (
        @(posedge clk)
        (protocol_select == 1'b0) |=> (out_data == out_data_t'($past(data_in)))
    );

    // Protocol 0 reports success.
    check_protocol0_status: assert property (
        @(posedge clk)
        (protocol_select == 1'b0) |=> (ack == 1'b1 && err == 1'b0)
    );

    // Protocol 1 outputs the inverted sampled input data.
    check_protocol1_out_data: assert property (
        @(posedge clk)
        (protocol_select == 1'b1) |=> (out_data == out_data_t'(~$past(data_in)))
    );

    // Protocol 1 reports success.
    check_protocol1_status: assert property (
        @(posedge clk)
        (protocol_select == 1'b1) |=> (ack == 1'b1 && err == 1'b0)
    );

    // An invalid protocol drives error and leaves out_data unchanged.
    check_invalid_protocol_response: assert property (
        @(posedge clk)
        ((protocol_select !== 1'b0) && (protocol_select !== 1'b1)) |=> (ack == 1'b0 && err == 1'b1 && out_data == $past(out_data))
    );

    // ack and err are always complementary after each update.
    check_ack_err_complementary: assert property (
        @(posedge clk)
        1'b1 |=> (ack ^ err)
    );

endmodule