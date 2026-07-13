

module s6(stage1_input,stage1_output);
input [5:0] stage1_input;
output [3:0] stage1_output;

reg [3:0] stage1_output;



always @(  stage1_input)

begin

   case(stage1_input)

        0: stage1_output = (12); 
        1: stage1_output = (10); 
        2: stage1_output = (1); 
        3: stage1_output = (15); 
        4: stage1_output = (10); 
        5: stage1_output = (4); 
        6: stage1_output = (15); 
        7: stage1_output = (2); 
        8: stage1_output = (9); 
        9: stage1_output = (7); 
        10: stage1_output = (2); 
        11: stage1_output = (12); 
        12: stage1_output = (6); 
        13: stage1_output = (9); 
        14: stage1_output = (8); 
        15: stage1_output = (5); 
        16: stage1_output = (0); 
        17: stage1_output = (6); 
        18: stage1_output = (13); 
        19: stage1_output = (1); 
        20: stage1_output = (3); 
        21: stage1_output = (13); 
        22: stage1_output = (4); 
        23: stage1_output = (14); 
        24: stage1_output = (14); 
        25: stage1_output = (0); 
        26: stage1_output = (7); 
        27: stage1_output = (11); 
        28: stage1_output = (5); 
        29: stage1_output = (3); 
        30: stage1_output = (11); 
        31: stage1_output = (8); 
        32: stage1_output = (9); 
        33: stage1_output = (4); 
        34: stage1_output = (14); 
        35: stage1_output = (3); 
        36: stage1_output = (15); 
        37: stage1_output = (2); 
        38: stage1_output = (5); 
        39: stage1_output = (12); 
        40: stage1_output = (2); 
        41: stage1_output = (9); 
        42: stage1_output = (8); 
        43: stage1_output = (5); 
        44: stage1_output = (12); 
        45: stage1_output = (15); 
        46: stage1_output = (3); 
        47: stage1_output = (10); 
        48: stage1_output = (7); 
        49: stage1_output = (11); 
        50: stage1_output = (0); 
        51: stage1_output = (14); 
        52: stage1_output = (4); 
        53: stage1_output = (1); 
        54: stage1_output = (10); 
        55: stage1_output = (7); 
        56: stage1_output = (1); 
        57: stage1_output = (6); 
        58: stage1_output = (13); 
        59: stage1_output = (0); 
        60: stage1_output = (11); 
        61: stage1_output = (8); 
        62: stage1_output = (6); 
        63: stage1_output = (13); 

endcase


	

end

endmodule
