module up_counter (
    input clk, 
    input reset,
    output reg [1:0] count
);

reg [1:0] next_count;

// Half adder
wire sum = count[0] ^ next_count[0];
wire carry_out = count[0] & next_count[0];

// D flip-flop
reg d;
always @(posedge carry_out or negedge reset) begin
    if (reset == 1'b0) begin
        d <= 2'b0;
    end else begin
        d <= sum;
    end
end

// Counter logic
always @(posedge clk or negedge reset) begin
    if (reset == 1'b0) begin
        count <= 2'b0;
    end else begin
        count <= next_count;
    end
end

// Next count logic
always @(*) begin
    if (count == 2'b11) begin
        next_count = 2'b0;
    end else begin
        next_count = count + 1;
    end
end

// Final output logic
wire final_output = (count == 2'b11) ? 1'b1 : 1'b0;

endmodule