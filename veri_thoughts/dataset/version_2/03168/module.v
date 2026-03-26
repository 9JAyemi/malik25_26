
module dff_rps(
    output reg Q,
    output Qbar,
    input D,
    input R,
    input S,
    input CLK
);
    // D flip-flop with synchronous reset and preset
    always @(posedge CLK) begin
        if (R) begin
            Q <= 1'b0;
        end else if (S) begin
            Q <= 1'b1;
        end else begin
            Q <= D;
        end
    end

    // Complementary output
    assign Qbar = ~Q;

endmodule
