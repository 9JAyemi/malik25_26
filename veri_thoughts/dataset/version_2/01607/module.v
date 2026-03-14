module dff_set (
    output reg Q,
    input CLK,
    input D,
    input SET_B
);

    // D Flip-Flop with Asynchronous Set
    always @(posedge CLK or negedge SET_B) begin
        if (!SET_B) begin
            Q <= 1'b1;  // Asynchronously set Q to 1 when SET_B is low
        end else begin
            Q <= D;     // Transfer D to Q on the rising edge of CLK
        end
    end

endmodule
