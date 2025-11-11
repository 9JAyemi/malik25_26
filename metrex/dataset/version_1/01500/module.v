

module debounce # (
  parameter pCLKS = 32'd 1_000_000) (
  input iCLK,
  input iRESET, input iSIG,
  output reg oSIG
);

integer debounceCtr = 0;

always @(posedge iCLK or posedge iRESET) begin
    if (iRESET)
    begin
        debounceCtr <= 0;
        oSIG <= 0;
    end
    else if (iSIG)
    begin if (!oSIG)
        begin if (debounceCtr < pCLKS)
            begin
                debounceCtr <= debounceCtr + 1;
                oSIG <= 0;
            end
            else
            begin
                debounceCtr <= 0;
                oSIG <= 1;
            end
        end
        else
        begin debounceCtr <= 0;
        end
    end
    else
    begin if (oSIG)
        begin
            if (debounceCtr < pCLKS)
            begin debounceCtr <= debounceCtr + 1;
                oSIG <= 1;
            end
            else
            begin
                debounceCtr <= 0;
                oSIG <= 0;
            end
        end
        else
        begin debounceCtr <= 0;
        end
    end
end

endmodule
