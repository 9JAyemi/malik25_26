module NegClockedOneShot(InputPulse, OneShot, Reset, CLOCK, Time);

input InputPulse, Reset, CLOCK;
input [7:0] Time;
output reg OneShot;

parameter State0=0, State1=1, State2=2;
reg [1:0] State;
reg [7:0] Counter;

always @ (posedge CLOCK) begin
    if (Reset == 1) begin
        State <= State0;
        Counter <= 0;
    end
    else begin
        case (State)
            State0: begin
                if (InputPulse == 0) begin
                    State <= State0;
                    Counter <= 0;
                end
                else begin
                    State <= State1;
                    Counter <= 0;
                end
            end
            State1: begin
                if (Counter < Time) begin
                    State <= State1;
                    Counter <= Counter + 1;
                end
                else begin
                    State <= State2;
                    Counter <= 0;
                end
            end
            State2: begin
                State <= State0;
                Counter <= 0;
            end
        endcase
    end
end

always @ (negedge InputPulse) begin
    if (Reset == 1) begin
        OneShot <= 0;
    end
    else begin
        if (State == State1) begin
            OneShot <= 1;
        end
        else begin
            OneShot <= 0;
        end
    end
end

endmodule