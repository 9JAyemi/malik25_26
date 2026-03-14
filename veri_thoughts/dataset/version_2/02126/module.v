
module full_adder (
        input A,    // Input A to the adder
        input B,    // Input B to the adder
        input Cin,  // Carry-in to the adder
        output Sum, // Output of the adder
        output Cout // Carry-out of the adder
    );

    assign Sum = A ^ B ^ Cin;
    assign Cout = (A & B) | (B & Cin) | (Cin & A);

endmodule

module ripple_carry_adder (
        input [3:0] A,    // Input A to the adder
        input [3:0] B,    // Input B to the adder
        input Cin,        // Carry-in to the adder
        output [3:0] Sum, // Output of the adder
        output Cout      // Carry-out of the adder
    );

    // Define internal wires
    wire [2:0] carry;

    // Instantiate full adder cells
    full_adder adder_0(.A(A[0]), .B(B[0]), .Cin(Cin), .Sum(Sum[0]), .Cout(carry[0]));
    full_adder adder_1(.A(A[1]), .B(B[1]), .Cin(carry[0]), .Sum(Sum[1]), .Cout(carry[1]));
    full_adder adder_2(.A(A[2]), .B(B[2]), .Cin(carry[1]), .Sum(Sum[2]), .Cout(carry[2]));
    full_adder adder_3(.A(A[3]), .B(B[3]), .Cin(carry[2]), .Sum(Sum[3]), .Cout(Cout));

endmodule

module up_down_counter (
        input clk,     // Clock input
        input reset,   // Synchronous active-high reset
        input Up,      // Up input to the counter
        input Down,    // Down input to the counter
        output [3:0] Q // Output of the counter
    );

    // Define internal registers
    reg [3:0] count;

    // Counter logic
    always @(posedge clk) begin
        if (reset) begin
            count <= 4'b0000; // Reset to zero
        end else begin
            if (Up && !Down) begin
                count <= count + 1'b1; // Increment on Up
            end else if (!Up && Down) begin
                count <= count - 1'b1; // Decrement on Down
            end
        end
    end

    // Output assignment
    assign Q = count;

endmodule
