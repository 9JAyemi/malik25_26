
module priority_encoder (
    input [15:0] data_in,
    output [1:0] priority_input,
    output [1:0] highest_input
);

    assign priority_input = (data_in[15] == 1) ? 2'b01 : (data_in[14] == 1) ? 2'b10 : 2'b00;
    assign highest_input = (priority_input == 2'b00) ? (data_in[0]) ? 2'b01 : 2'b00 : (priority_input == 2'b01) ? (data_in[1]) ? 2'b10 : 2'b01 : (data_in[2]) ? 2'b11 : 2'b10;

endmodule
