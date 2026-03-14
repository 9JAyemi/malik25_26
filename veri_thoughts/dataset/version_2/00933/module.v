
module top_module(
    input a,
    input b,
    input [1:0] sel2, // select input for the second multiplexer
    input [3:0] data2_0, // input data for the second multiplexer
    input [3:0] data2_1, // input data for the second multiplexer
    input [1:0] sel1, // select input for the first multiplexer
    input [3:0] data1_0, // input data for the first multiplexer
    input [3:0] data1_1, // input data for the first multiplexer
    input [3:0] data1_2, // input data for the first multiplexer
    input [3:0] data1_3, // input data for the first multiplexer
    input [3:0] data1_4, // input data for the first multiplexer
    input [3:0] data1_5, // input data for the first multiplexer
    output out_wire // output of the XOR gate
);

// Priority encoder for the first multiplexer
wire [2:0] priority_enc;
assign priority_enc = {data1_0[3], data1_1[3], data1_2[3], data1_3[3], data1_4[3], data1_5[3]};

// First multiplexer
wire [3:0] mux1_out_wire;
assign mux1_out_wire = (sel1 == 2'b00) ? data1_0 :
                      (sel1 == 2'b01) ? data1_1 :
                      (sel1 == 2'b10) ? data1_2 :
                      (sel1 == 2'b11) ? data1_3 : 0; // Default value for cases that are not covered

// Priority encoder for the second multiplexer
wire [1:0] priority_enc2;
assign priority_enc2 = {data2_0[3], data2_1[3]};

// Second multiplexer
wire [3:0] mux2_out_wire;
assign mux2_out_wire = (sel2 == 2'b00) ? data2_0[1:0] :
                       (sel2 == 2'b01) ? data2_0[3:2] :
                       (sel2 == 2'b10) ? data2_1[1:0] :
                       (sel2 == 2'b11) ? data2_1[3:2] : 0; // Default value for cases that are not covered

// XOR gate
wire xor_out_wire;
assign xor_out_wire = a ^ b;

// Output
assign out_wire = xor_out_wire;

endmodule
