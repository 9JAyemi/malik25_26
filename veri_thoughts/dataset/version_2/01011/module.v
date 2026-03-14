module decade_counter_mux (
    input clk,
    input slowena,
    input reset,
    input a,
    input b,
    input sel,
    output [7:0] out
);

reg [3:0] count;
wire enable;

// Decade Counter
always @(posedge clk or negedge reset) begin
    if (reset == 0) begin
        count <= 0;
    end else if (slowena == 1) begin
        if (count == 9) begin
            count <= 0;
        end else begin
            count <= count + 1;
        end
    end
end

// Multiplexer
assign enable = (sel == 0) ? a : b;

// Functional Module
assign out = count + enable;

endmodule