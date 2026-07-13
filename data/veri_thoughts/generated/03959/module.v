
module xor_gate(
    input       [99:0]  data_in_1   ,
    input       [7:0]   data_in_2   ,
    output wire [99:0]  data_out
);

    assign data_out = data_in_1 ^ {92'b0, data_in_2};

endmodule
