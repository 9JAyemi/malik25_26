module Ramifier
#(
    parameter BRANCH_CONDITION_WIDTH = 4
)(
  input [(BRANCH_CONDITION_WIDTH - 1):0] condition,
  input negative_flag, zero_flag, carry_flag, overflow_flag,
  output reg take
);


    always @ ( * ) begin
        case (condition)
            0:begin take = zero_flag;
            end
            1:begin take = !zero_flag;
            end
            2:begin take = carry_flag;
            end
            3:begin take = !carry_flag;
            end
            4:begin   take = negative_flag;
            end
            5:begin   take = !(negative_flag);
            end
            6:begin   take = overflow_flag;
            end
            7:begin   take = !(overflow_flag);
            end
            8:begin   take = (carry_flag) && (!zero_flag);
            end
            9:begin   take = (!carry_flag) || (zero_flag);
            end
            10:begin    take =  (negative_flag ^~ overflow_flag) ;
            end
            11:begin    take = (negative_flag ^ overflow_flag);
            end
            12:begin    take = (!zero_flag) && (negative_flag ^~ overflow_flag);
            end
            13:begin     take = (zero_flag) || (negative_flag ^ overflow_flag);
            end
            14:begin  take = 1;
            end
            default: begin
                take = 0; end
        endcase
    end

endmodule
