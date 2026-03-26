
module mux_encoder (
    input [3:0] A,
    input [3:0] B,
    input [3:0] C,
    input [3:0] D,
    input [1:0] SEL,
    output [3:0] Q
);

reg [3:0] Q_reg;
reg [3:0] highest_priority_input;

// Priority encoder
always @*
begin
    if (D >= C && D >= B && D >= A)
        highest_priority_input = D;
    else if (C >= B && C >= A)
        highest_priority_input = C;
    else if (B >= A)
        highest_priority_input = B;
    else
        highest_priority_input = A;
end

// Multiplexer
always @*
begin
    case (SEL)
        2'b00: Q_reg = A;
        2'b01: Q_reg = B;
        2'b10: Q_reg = C;
        2'b11: Q_reg = D;
        default: Q_reg = 4'b0; // default case to prevent conflicting drivers
    endcase
end

// Output the highest priority input if multiple inputs are high
assign Q = highest_priority_input | Q_reg;

endmodule