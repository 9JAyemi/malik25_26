
module up_down_counter (
    input clk,
    input reset,
    input enable,
    input up_down,
    output reg [3:0] count
);
    
    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (enable) begin
            if (up_down) begin
                count <= count + 1;
            end else if (count > 0) begin
                count <= count - 1;
            end
        end
    end
    
endmodule
module shift_register (
    input clk,
    input reset,
    input load,
    input [3:0] data_in,
    output reg [3:0] data_out
);
    
    reg [3:0] shift_reg;
    
    always @(posedge clk) begin
        if (reset) begin
            shift_reg <= 0;
        end else if (load) begin
            shift_reg <= data_in;
        end else begin
            shift_reg <= {shift_reg[3:1], 1'b0};
        end
    end
    
    always@(*) begin
        data_out <= shift_reg;
    end
    
endmodule
module top_module (
    input clk,
    input reset,
    input up_down,
    input load,
    input [3:0] data_in,
    output [3:0] data_out
);
    
    reg enable;
    wire [3:0] count;
    
    up_down_counter counter (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .up_down(up_down),
        .count(count)
    );
    
    shift_register shift_reg (
        .clk(clk),
        .reset(reset),
        .load(load),
        .data_in(count),
        .data_out(data_out)
    );
    
    always @(posedge clk) begin
        enable <= !load;
    end
    
endmodule