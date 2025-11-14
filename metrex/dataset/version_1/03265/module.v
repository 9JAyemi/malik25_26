
module xnor_gate(
    input A,
    input B,
    input VPWR,
    input VGND,
    output Y
);

    reg [3:0] state = 4'b0000;
    reg [1:0] input_state = 2'b00;
    wire [1:0] xnor_out;

    assign xnor_out = {~A ^ ~B, ~A ^ ~B};
    assign Y = input_state == 2'b00 ? xnor_out[0] :
               input_state == 2'b01 ? xnor_out[1] :
               input_state == 2'b10 ? xnor_out[0] & xnor_out[1] :
               ~xnor_out[0] & ~xnor_out[1];

endmodule