
module _4bit_down_counter_with_synch_load_enable_clear(
    input Clock, Clear, Enable, Load,
    output reg [3:0] Q
);

always @(posedge Clock) begin
    if (Clear) begin
        Q <= 4'b1111;
    end else if (Enable) begin
        Q <= Q - 1;
    end else if (Load) begin
        Q <= 4'b1111;
    end
end

endmodule