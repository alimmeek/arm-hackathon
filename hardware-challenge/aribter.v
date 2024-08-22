module arbiter (
    input  wire clk,
    input  wire resetn,

    input  wire [2:0] r,
    
    output wire [2:0] g
);

parameter A = 2'b00, B = 2'b01, C = 2'b10, D = 2'b11;

wire [1:0] next_state;
reg [1:0] curr_state;

wire [2:0] g_next;
reg [2:0] g_q;

always @* begin
    next_state = curr_state;
    case (curr_state)
        A : begin
            if (r[0]) begin
                next_state = B;
            end else if (r[1]) begin
                next_state = C;
            end else if (r[2]) begin
                next_state = D;
            end
        end

        B : begin
            if (~r[0]) begin
                next_state = A;
            end
        end

        C : begin
            if (~r[1]) begin
                next_state = A;
            end
        end

        D : begin
            if (~r[2]) begin
                next_state = A;
            end
        end
    endcase
end

always @* begin
    g_next = g_q;
    case (curr_state)
        A : g_next = 3'b000;

        B : g_next = 3'b001;

        C : g_next = 3'b010;

        D : g_next = 3'b100;
    endcase
end

always @(posedge clk or negedge resetn) begin
    if (~resetn) begin
        curr_state <= A;
        g_q <= 3'b000;
    end else begin
        curr_state <= next_state;
        g_q <= g_next;
    end
end

assign g = g_q;

endmodule