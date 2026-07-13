module add_sub (
    input clk,
    input reset,      // Synchronous active-low reset
    input [3:0] A,
    input [3:0] B,
    input sub,
    output [3:0] q
);
    reg [3:0] result;
    
    always @(posedge clk, negedge reset) begin
        if (reset == 0) begin
            result <= 4'b0;
        end else begin
            if (sub == 1) begin
                result <= A - B;
            end else begin
                result <= A + B;
            end
        end
    end
    
    assign q = result;
    
endmodule

module priority_encoder (
    input [3:0] I,
    input enable,     // Active high enable
    output [1:0] q
);
    assign q = (enable == 1) ? {I[3], I[2]} :
                              (enable == 1) ? {I[3], I[1]} :
                                               {I[3], I[0]};
endmodule

module functional_module (
    input [3:0] add_sub_result,
    input [1:0] priority_encoder_D,
    output [3:0] q
);
    assign q = add_sub_result & priority_encoder_D;
endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-low reset
    input [3:0] A,
    input [3:0] B,
    input sub,
    input [3:0] I,
    input enable,     // Active high enable for priority_encoder
    output [3:0] q
);
    wire [3:0] add_sub_result;
    wire [1:0] priority_encoder_D;
    
    add_sub add_sub_inst (
        .clk(clk),
        .reset(reset),
        .A(A),
        .B(B),
        .sub(sub),
        .q(add_sub_result)
    );
    
    priority_encoder priority_encoder_inst (
        .I(I),
        .enable(enable),
        .q(priority_encoder_D)
    );
    
    functional_module functional_module_inst (
        .add_sub_result(add_sub_result),
        .priority_encoder_D(priority_encoder_D),
        .q(q)
    );
    
endmodule