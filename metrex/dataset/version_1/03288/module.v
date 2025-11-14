
module shifter (
    input [3:0] data_in,
    input select,
    output [4:0] data_out
);

    assign data_out = select ? {data_in[3], data_in[2:0]} : {data_in[1:0], data_in[3:2]};
    
endmodule
module next_power_of_two (
    input [4:0] data_in,
    output [4:0] data_out
);

    assign data_out = (data_in == 5'b00001) ? 5'b00010 :
                      (data_in <= 5'b00010) ? 5'b00100 :
                      (data_in <= 5'b00100) ? 5'b01000 :
                      (data_in <= 5'b01000) ? 5'b10000 :
                      5'b10000;
    
endmodule
module top_module (
    input [3:0] data,
    input rotate,
    input select,
    output [4:0] result
);

    wire [4:0] shifted_data;
    wire [4:0] next_power;
    
    shifter shifter_inst (
        .data_in(data),
        .select(rotate),
        .data_out(shifted_data)
    );
    
    next_power_of_two next_power_inst (
        .data_in(shifted_data),
        .data_out(next_power)
    );
    
    assign result = next_power;
    
endmodule