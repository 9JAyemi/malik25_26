module accu(
    input               clk         ,   
    input               rst_n       ,
    input       [7:0]   data_in     ,
    input               valid_a     ,
    input               ready_b     ,
 
    output              ready_a     ,
    output  reg         valid_b     ,
    output  reg [9:0]   data_out
);

reg [7:0] input_reg;
reg [3:0] counter;
reg [9:0] accu_result;

always @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
        input_reg <= 8'b0;
        counter <= 4'b0;
        accu_result <= 10'b0;
        valid_b <= 1'b0;
    end
    else begin
        if(valid_a && ready_b) begin
            input_reg <= data_in;
            counter <= counter + 1;
            accu_result <= accu_result + data_in;
        end
        if(counter == 4) begin
            data_out <= accu_result;
            accu_result <= 10'b0;
            counter <= 4'b0;
            valid_b <= 1'b1;
        end
        else begin
            data_out <= 10'b0;
            valid_b <= 1'b0;
        end
    end
end

assign ready_a = !valid_b;

endmodule