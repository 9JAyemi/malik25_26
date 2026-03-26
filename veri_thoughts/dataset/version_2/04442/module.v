
module digital_circuit (
    input input_1,
    input input_2,    
    input input_3,    
    input input_4,    
    output output_1,    
    output output_2    
);

    // Implement output_1 as the AND of input_1 and input_2
    assign output_1 = input_1 & input_2;
    
    // Implement output_2 as the OR of input_3 and input_4
    assign output_2 = input_3 | input_4;
    
endmodule
