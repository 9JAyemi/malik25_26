
module xor_module(
    input [2:0] in_data,
    output [2:0] out_xor,
    output [2:0] out_inv
);
    assign out_xor = in_data ^ 3'b111;
    assign out_inv = ~in_data;
endmodule
module top_module( 
    input [2:0] a,
    input [2:0] b,
    input valid_a,
    input ready_b,
    output reg valid_b,
    output [2:0] out_or_bitwise,
    output out_or_logical,
    output reg [5:0] out_not
);

    wire [2:0] out_xor_a;
    wire [2:0] out_xor_b;
    wire [2:0] inv_a;
    wire [2:0] inv_b;
    wire not_ready_b;

    xor_module xor_a(.in_data(a), .out_xor(out_xor_a), .out_inv(inv_a));
    xor_module xor_b(.in_data(b), .out_xor(out_xor_b), .out_inv(inv_b));

    assign out_or_bitwise = out_xor_a | out_xor_b;

    assign out_or_logical = (|out_or_bitwise);

    always @(posedge valid_a) begin
        if (ready_b) begin
            valid_b <= 1;
            out_not <= {inv_a, inv_b};
        end
        else
            valid_b <= 0;
    end

    assign not_ready_b = ~ready_b;
    assign ready_b = not_ready_b;

endmodule