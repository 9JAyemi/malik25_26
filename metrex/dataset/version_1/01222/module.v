
module top_module (
    input clk,
    input reset,      // Asynchronous active-high reset
    input a,           // 1-bit input for edge detection
    output [3:0] counter_out,  // 4-bit output from the counter
    output reg rise,   // Output indicating rising edge detection
    output reg down,   // Output indicating falling edge detection
    output [3:0] final_out  // 4-bit output from the functional module
);

reg [3:0] counter;
reg [1:0] edge_detect;
reg [1:0] edge_detect_prev;

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        counter <= 4'b1000; // Reset to 8
    end else begin
        counter <= counter + 1;
    end
end

always @(posedge clk) begin
    edge_detect_prev <= edge_detect;
    edge_detect <= {edge_detect[0], a} ^ {edge_detect_prev[0], edge_detect_prev[1]};
    rise <= edge_detect[1] & !edge_detect_prev[1];
    down <= !edge_detect[1] & edge_detect_prev[1];
end

assign final_out = counter + rise - down;
assign counter_out = counter;

endmodule
