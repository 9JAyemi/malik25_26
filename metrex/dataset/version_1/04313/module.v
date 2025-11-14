
module xor_module (
    input a,
    input b,
    input clk,
    output reg out_comb_ff
);
    always @(posedge clk) begin
        out_comb_ff <= a ^ b;
    end
endmodule
module edge_detection (
    input a,
    input clk,
    output reg rising_edge,
    output reg falling_edge
);
    parameter IDLE = 2'b00, RISING = 2'b01, FALLING = 2'b10;
    reg [1:0] state, next_state;
    
    always @(posedge clk) begin
        state <= next_state;
    end
    
    always @(*) begin
        case (state)
            IDLE: begin
                if (a) begin
                    next_state = RISING;
                end else begin
                    next_state = IDLE;
                end
            end
            RISING: begin
                if (a) begin
                    next_state = RISING;
                end else begin
                    next_state = FALLING;
                end
            end
            FALLING: begin
                if (a) begin
                    next_state = RISING;
                end else begin
                    next_state = FALLING;
                end
            end
        endcase
    end
    
    always @(posedge clk) begin
        case (state)
            IDLE: begin
                rising_edge <= 1'b0;
                falling_edge <= 1'b0;
            end
            RISING: begin
                rising_edge <= 1'b1;
                falling_edge <= 1'b0;
            end
            FALLING: begin
                rising_edge <= 1'b0;
                falling_edge <= 1'b1;
            end
        endcase
    end
endmodule
module final_module (
    input out_comb_ff,
    input rising_edge,
    input falling_edge,
    output reg [1:0] final_output
);
    always @* begin
        if (out_comb_ff && rising_edge) begin
            final_output = 2'b10;
        end else if (out_comb_ff || rising_edge || falling_edge) begin
            final_output = 2'b01;
        end else begin
            final_output = 2'b00;
        end
    end
endmodule
module top_module (
    input clk,
    input rst_n,
    input a,
    input b,
    output out_comb_ff,
    output [1:0] final_output
);
    reg rising_edge, falling_edge;
    wire out_comb_ff_wire;
    wire rising_edge_wire, falling_edge_wire;
    
    xor_module xor_inst (
        .a(a),
        .b(b),
        .clk(clk),
        .out_comb_ff(out_comb_ff_wire)
    );
    
    edge_detection edge_inst (
        .a(a),
        .clk(clk),
        .rising_edge(rising_edge_wire),
        .falling_edge(falling_edge_wire)
    );
    
    final_module final_inst (
        .out_comb_ff(out_comb_ff_wire),
        .rising_edge(rising_edge_wire),
        .falling_edge(falling_edge_wire),
        .final_output(final_output)
    );
    
    assign out_comb_ff = out_comb_ff_wire;
    
endmodule