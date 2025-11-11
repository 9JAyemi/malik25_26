module top_module (
    input [15:0] data_in, // Input for binary ones counter module
    input [3:0] LOAD, // Input for up-down counter module
    output [3:0] Q, // Output from up-down counter module
    output [3:0] ones_count, // Output from binary ones counter module
    output [3:0] final_output // Final output after adding both module outputs
);

// Instantiate binary ones counter module
binary_ones_counter boc (
    .data_in(data_in),
    .ones_count(ones_count)
);

// Instantiate up-down counter module
up_down_counter udc (
    .LOAD(LOAD),
    .Q(Q)
);

// Instantiate adder module
adder add (
    .A(ones_count),
    .B(Q),
    .SUM(final_output)
);

endmodule

// Binary ones counter module
module binary_ones_counter (
    input [15:0] data_in,
    output [3:0] ones_count
);

assign ones_count = data_in[0] + data_in[1] + data_in[2] + data_in[3] + data_in[4] + data_in[5] + data_in[6] + data_in[7] + data_in[8] + data_in[9] + data_in[10] + data_in[11] + data_in[12] + data_in[13] + data_in[14] + data_in[15];

endmodule

// Up-down counter module
module up_down_counter (
    input [3:0] LOAD,
    output [3:0] Q
);

reg [3:0] count;
always @(LOAD) begin
    count <= LOAD;
end

assign Q = count;

endmodule

// Adder module
module adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] SUM
);

assign SUM = A + B;

endmodule