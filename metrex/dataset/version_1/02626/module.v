module MaquinaDeControl(
    input Clock,
    input Reset,
    input NewScanCode,
    input NewAscii,
    output reg LoadDato,
    output reg LoadChar,
    output reg ScanCodeType
);

reg [1:0] state;
parameter Sleep = 3'h0;
parameter Recibido = 3'h1;
parameter Type = 3'h3;
parameter New = 3'h2;

always @(posedge Clock or negedge Reset) begin
    if (!Reset) begin
        state <= Sleep;
    end else begin
        case (state)
            Sleep: begin
                if (NewScanCode) begin
                    state <= Recibido;
                end else begin
                    state <= Sleep;
                end
            end
            Recibido: begin
                state <= Type;
            end
            Type: begin
                if (NewAscii && !Reset) begin
                    state <= New;
                end else if (!NewAscii || Reset) begin
                    state <= Sleep;
                end
            end
            New: begin
                state <= Sleep;
            end
            default: begin
                state <= Sleep;
            end
        endcase
    end
end

always @(state) begin
    case (state)
        Sleep: begin
            LoadDato <= 0;
            LoadChar <= 0;
            ScanCodeType <= 0;
        end
        Recibido: begin
            LoadDato <= 1;
            LoadChar <= 0;
            ScanCodeType <= 0;
        end
        Type: begin
            LoadDato <= 0;
            LoadChar <= 0;
            ScanCodeType <= 1;
        end
        New: begin
            LoadDato <= 0;
            LoadChar <= 1;
            ScanCodeType <= 0;
        end
        default: begin
            LoadDato <= 0;
            LoadChar <= 0;
            ScanCodeType <= 0;
        end
    endcase
end

endmodule