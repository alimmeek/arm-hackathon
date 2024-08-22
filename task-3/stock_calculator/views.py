from django.shortcuts import render
import requests
from datetime import datetime

# Create your views here.
def dashboard(request):
    if request.method == 'POST':
        amount = request.POST.get('amount')
        date = request.POST.get('date')
        
        api_key = 'demo'

        if not amount or not date:
            error_message = "Both amount and date fields are required."
            return render(request, 'dashboard.html', {'error_message': error_message})        

        # Get all data for the month. (It doesn't let us get the data for a specific day.)
        r = requests.get(f"https://www.alphavantage.co/query?function=TIME_SERIES_INTRADAY&symbol=IBM&interval=5min&month={date[0:-3]}&outputsize=full&apikey={api_key}")
        data = r.json()

        # Extract the time series
        time_series = data["Time Series (5min)"]

        # The date will have multiple keys (2009-01-01 08:00, 2009-01-01 08:05, etc.).
        all_keys_for_date = [key for key in time_series.keys() if key.startswith(date)]

        # If data for the date doesn't exist, then return an error.
        if len(all_keys_for_date) == 0:
            return render(request, 'dashboard.html', {'error_message': "There is no data for that date."}) 

        # Get the earliest key for the date (as there are multiple, e.g., 2009-01-01 08:00, 2009-01-01 08:05).
        earliest_key_for_date = all_keys_for_date[-1]
        open_stock_value = time_series[earliest_key_for_date]['1. open']

        fraction_of_stock = float(amount) / float(open_stock_value)

        # Get today's stock value, multiply it by fraction_of_stock, and get result - converted_amount
        r = requests.get(f"https://www.alphavantage.co/query?function=TIME_SERIES_INTRADAY&symbol=IBM&interval=5min&outputsize=full&apikey={api_key}")
        data = r.json()

        # Extract the time series
        latest_time_series = data["Time Series (5min)"]
        latest_date = next(iter(latest_time_series))
        latest_open_stock_value = latest_time_series[latest_date]['1. open']

        difference = (float(latest_open_stock_value) * fraction_of_stock) - float(amount)
        if difference >= 0:
            output_data = f"You gained £{abs(difference)}."
        else:
            output_data = f"You lost £{abs(difference)}."

        return render(request, 'dashboard.html', {'output_data': output_data, 'date': date, 'open': open_stock_value, 'latest_open': latest_open_stock_value, 'amount': amount})

    return render(request, 'dashboard.html')