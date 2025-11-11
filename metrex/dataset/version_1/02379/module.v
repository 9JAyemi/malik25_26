module assert_change_assert (
  input clk, reset_n, start_event, xzcheck_enable,
  input [width-1:0] test_expr,
  input [31:0] window,
  input ignore_new_start, reset_on_new_start, error_on_new_start,
  output pass
);
  parameter width = 8;
  parameter num_cks = 2;
  reg [width-1:0] test_expr_reg;
  reg [31:0] window_count;
  reg [31:0] start_event_count;
  reg [31:0] reset_event_count;
  reg [31:0] error_event_count;
  reg [31:0] xzcheck_event_count;
  reg [31:0] xz_error_count;
  reg [31:0] xz_ignore_count;
  reg [31:0] xz_pass_count;
  reg [31:0] xz_reset_count;
  reg [1:0] state;
  reg [1:0] xz_state;
  reg [width-1:0] xz_value;
  reg [width-1:0] xz_mask;
  reg [width-1:0] xz_error_mask;
  reg [width-1:0] xz_ignore_mask;
  reg [width-1:0] xz_pass_mask;
  reg [width-1:0] xz_reset_mask;
  assign pass = (state == 2'b10);
  
  always @(posedge clk) begin
    if (!reset_n) begin
      state <= 2'b00;
      xz_state <= 2'b00;
      test_expr_reg <= 0;
      window_count <= 0;
      start_event_count <= 0;
      reset_event_count <= 0;
      error_event_count <= 0;
      xzcheck_event_count <= 0;
      xz_error_count <= 0;
      xz_ignore_count <= 0;
      xz_pass_count <= 0;
      xz_reset_count <= 0;
      xz_value <= 0;
      xz_mask <= 0;
      xz_error_mask <= 0;
      xz_ignore_mask <= 0;
      xz_pass_mask <= 0;
      xz_reset_mask <= 0;
    end else begin
      case (state)
        2'b00: begin // IDLE
          test_expr_reg <= test_expr;
          if (start_event) begin
            start_event_count <= start_event_count + 1;
            if (ignore_new_start) begin
              state <= 2'b01; // IGNORE
            end else begin
              state <= 2'b10; // CHECK
            end
          end
        end
        2'b01: begin // IGNORE
          if (start_event) begin
            start_event_count <= start_event_count + 1;
            if (reset_on_new_start) begin
              reset_event_count <= reset_event_count + 1;
              state <= 2'b00; // IDLE
            end else if (error_on_new_start) begin
              error_event_count <= error_event_count + 1;
              state <= 2'b11; // ERROR
            end
          end else begin
            window_count <= window_count + 1;
            if (window_count >= window) begin
              state <= 2'b00; // IDLE
            end
          end
        end
        2'b10: begin // CHECK
          if (start_event) begin
            start_event_count <= start_event_count + 1;
            if (reset_on_new_start) begin
              reset_event_count <= reset_event_count + 1;
              state <= 2'b00; // IDLE
            end else if (error_on_new_start) begin
              error_event_count <= error_event_count + 1;
              state <= 2'b11; // ERROR
            end
          end else begin
            window_count <= window_count + 1;
            if (window_count >= window) begin
              state <= 2'b00; // IDLE
            end else begin
              if (xzcheck_enable) begin
                case (xz_state)
                  2'b00: begin // IDLE
                    if (test_expr_reg[xzcheck_event_count]) begin
                      xz_value <= test_expr_reg;
                      xz_mask <= (1 << xzcheck_event_count);
                      xz_state <= 2'b01; // ERROR_MASK
                    end else begin
                      xz_state <= 2'b00; // IDLE
                      xzcheck_event_count <= xzcheck_event_count + 1;
                      if (xzcheck_event_count >= width) begin
                        xz_pass_count <= xz_pass_count + 1;
                        xz_state <= 2'b10; // PASS
                      end
                    end
                  end
                  2'b01: begin // ERROR_MASK
                    if (test_expr_reg[xzcheck_event_count]) begin
                      xz_error_mask <= xz_error_mask | (1 << xzcheck_event_count);
                    end else begin
                      xz_ignore_mask <= xz_ignore_mask | (1 << xzcheck_event_count);
                    end
                    xzcheck_event_count <= xzcheck_event_count + 1;
                    if (xzcheck_event_count >= width) begin
                      xz_state <= 2'b10; // PASS
                    end else if (test_expr_reg[xzcheck_event_count]) begin
                      xz_value <= test_expr_reg;
                      xz_mask <= (1 << xzcheck_event_count);
                      xz_state <= 2'b01; // ERROR_MASK
                    end else begin
                      xz_state <= 2'b00; // IDLE
                    end
                  end
                  2'b10: begin // PASS
                    if (test_expr_reg[xzcheck_event_count]) begin
                      if (xz_value[xzcheck_event_count] !== test_expr_reg[xzcheck_event_count]) begin
                        xz_error_count <= xz_error_count + 1;
                        xz_error_mask <= xz_error_mask | (1 << xzcheck_event_count);
                      end else begin
                        xz_pass_mask <= xz_pass_mask | (1 << xzcheck_event_count);
                      end
                      xz_reset_mask <= xz_reset_mask | (1 << xzcheck_event_count);
                      xz_reset_count <= xz_reset_count + 1;
                      xz_state <= 2'b00; // IDLE
                      xzcheck_event_count <= xzcheck_event_count + 1;
                      if (xzcheck_event_count >= width) begin
                        xz_pass_count <= xz_pass_count + 1;
                        xz_state <= 2'b10; // PASS
                      end
                    end else begin
                      xz_state <= 2'b00; // IDLE
                      xzcheck_event_count <= xzcheck_event_count + 1;
                      if (xzcheck_event_count >= width) begin
                        xz_pass_count <= xz_pass_count + 1;
                        xz_state <= 2'b10; // PASS
                      end
                    end
                  end
                endcase
              end else begin
                if (test_expr_reg === 0) begin
                  state <= 2'b11; // ERROR
                end
              end
            end
          end
        end
        2'b11: begin // ERROR
          if (start_event) begin
            start_event_count <= start_event_count + 1;
            if (reset_on_new_start) begin
              reset_event_count <= reset_event_count + 1;
              state <= 2'b00; // IDLE
            end else if (error_on_new_start) begin
              error_event_count <= error_event_count + 1;
              state <= 2'b11; // ERROR
            end
          end else begin
            window_count <= window_count + 1;
            if (window_count >= window) begin
              state <= 2'b00; // IDLE
            end
          end
        end
      endcase
    end
  end
endmodule