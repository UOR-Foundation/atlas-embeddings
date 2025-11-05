// Simple client-side search implementation for Jekyll site
(function() {
  var searchIndex = null;
  var searchInput = document.getElementById('search-input');
  var searchResults = document.getElementById('search-results');
  
  // Load search index
  function loadSearchIndex() {
    var xhr = new XMLHttpRequest();
    xhr.open('GET', '/atlas-12288/search.json', true);
    xhr.onload = function() {
      if (xhr.status === 200) {
        searchIndex = JSON.parse(xhr.responseText);
      }
    };
    xhr.send();
  }
  
  // Perform search
  function search(query) {
    if (!searchIndex || query.length < 2) {
      hideResults();
      return;
    }
    
    var results = [];
    var queryLower = query.toLowerCase();
    
    searchIndex.forEach(function(page) {
      var titleMatch = page.title.toLowerCase().indexOf(queryLower);
      var contentMatch = page.content.toLowerCase().indexOf(queryLower);
      var score = 0;
      
      if (titleMatch !== -1) {
        score += 10;
        if (titleMatch === 0) score += 5;
      }
      
      if (contentMatch !== -1) {
        score += 5;
        // Extract snippet around match
        var start = Math.max(0, contentMatch - 50);
        var end = Math.min(page.content.length, contentMatch + 100);
        page.snippet = '...' + page.content.substring(start, end).replace(/\n/g, ' ') + '...';
      }
      
      if (score > 0) {
        page.score = score;
        results.push(page);
      }
    });
    
    // Sort by score
    results.sort(function(a, b) {
      return b.score - a.score;
    });
    
    displayResults(results.slice(0, 10));
  }
  
  // Display search results
  function displayResults(results) {
    if (!searchResults) {
      // Create results dropdown if it doesn't exist
      searchResults = document.createElement('div');
      searchResults.id = 'search-results';
      searchResults.className = 'search-results';
      searchInput.parentNode.appendChild(searchResults);
    }
    
    if (results.length === 0) {
      searchResults.innerHTML = '<div class="no-results">No results found</div>';
    } else {
      var html = '<ul>';
      results.forEach(function(result) {
        html += '<li>';
        html += '<a href="' + result.url + '">';
        html += '<strong>' + result.title + '</strong>';
        if (result.snippet) {
          html += '<br><span class="snippet">' + result.snippet + '</span>';
        }
        html += '</a>';
        html += '</li>';
      });
      html += '</ul>';
      searchResults.innerHTML = html;
    }
    
    searchResults.style.display = 'block';
  }
  
  // Hide search results
  function hideResults() {
    if (searchResults) {
      searchResults.style.display = 'none';
    }
  }
  
  // Initialize
  if (searchInput) {
    loadSearchIndex();
    
    // Search on input
    searchInput.addEventListener('input', function(e) {
      search(e.target.value);
    });
    
    // Hide results on click outside
    document.addEventListener('click', function(e) {
      if (!searchInput.contains(e.target) && !searchResults.contains(e.target)) {
        hideResults();
      }
    });
    
    // Prevent form submission
    searchInput.addEventListener('keydown', function(e) {
      if (e.key === 'Enter') {
        e.preventDefault();
        var firstResult = searchResults.querySelector('a');
        if (firstResult) {
          window.location.href = firstResult.href;
        }
      }
    });
  }
})();