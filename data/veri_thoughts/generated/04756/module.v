
module shift_register (
    input [3:0] D, // Data input
    input LD, // Load input
    input CLK, // Clock input
    input CLR, // Clear input
    output reg [3:0] Q // Data output
);

    always @(posedge CLK, posedge CLR) begin
        if (CLR) begin
            Q <= 4'b0000; // Reset to all zeros
        end else if (LD) begin
            Q <= D; // Load data into register
        end else begin
            Q <= {Q[2:0], Q[3]}; // Shift data left
        end
    end

endmodule
module adder (
    input [3:0] A, B,
    output [3:0] sum
);

    assign sum = A + B;

endmodule
module top_module (
    input [3:0] D1, D2,
    input LD1, LD2, CLK, CLR,
    output [3:0] sum
);

    wire [3:0] Q1, Q2; // Declare wires for shift register outputs

    shift_register sr1 (
        .D(D1),
        .LD(LD1),
        .CLK(CLK),
        .CLR(CLR),
        .Q(Q1) // Connect wire to shift_register output
    );

    shift_register sr2 (
        .D(Q1),
        .LD(LD2),
        .CLK(CLK),
        .CLR(CLR),
        .Q(Q2) // Connect wire to shift_register output
    );

    adder add (
        .A(Q1),
        .B(Q2),
        .sum(sum)
    );

endmodule