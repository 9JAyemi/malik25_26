module decade_counter (
    input clk,
    input pause,
    input reset,
    output reg [3:0] q
);

reg [3:0] johnson;
reg [3:0] johnson_next;
reg flip_flop;

always @ (posedge clk) begin
    if (reset) begin
        johnson <= 4'b0001;
        flip_flop <= 1'b0;
        q <= 4'b0000;
    end else if (pause) begin
        johnson_next <= johnson;
    end else begin
        johnson_next[0] <= johnson[3];
        johnson_next[1] <= johnson[0];
        johnson_next[2] <= johnson[1];
        johnson_next[3] <= johnson[2] ^ johnson[3];
        johnson <= johnson_next;
        
        if (johnson == 4'b1001) begin
            flip_flop <= ~flip_flop;
        end
        
        if (flip_flop) begin
            q <= 4'b0000;
        end else begin
            q <= johnson;
        end
    end
end

endmodule

module top_module (
    input clk,
    input pause,
    input reset,
    output [3:0] q
);

decade_counter counter (
    .clk(clk),
    .pause(pause),
    .reset(reset),
    .q(q)
);

endmodule